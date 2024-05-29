use core::{
  fmt,
  mem::{self, MaybeUninit},
  ptr,
};

use crossbeam_epoch::{Atomic, Collector, Guard, Owned};
use crossbeam_utils::Backoff;

use super::sync::*;

mod iterator;
pub use iterator::*;

struct Ref<T> {
  value: T,
  refs: AtomicUsize,
}

impl<T> Ref<T> {
  #[inline]
  fn new(value: T, refs: usize) -> Self {
    Self {
      value,
      refs: AtomicUsize::new(refs),
    }
  }
}

struct RawNode<T> {
  /// The value of the node
  value: MaybeUninit<Ref<T>>,

  /// The next node in the linked list
  next: Atomic<RawNode<T>>,
}

impl<T> RawNode<T> {
  const UNINIT: Self = Self {
    value: MaybeUninit::uninit(),
    next: Atomic::null(),
  };

  /// Create a new node
  #[inline]
  fn new(value: T, refs: usize) -> Self {
    RawNode {
      value: MaybeUninit::new(Ref::new(value, refs)),
      next: Atomic::null(),
    }
  }

  /// Attempts to increment the reference count of a node and returns `true` on success.
  ///
  /// The reference count can be incremented only if it is non-zero.
  ///
  /// # Panics
  ///
  /// Panics if the reference count overflows.
  #[inline]
  unsafe fn try_increment(&self) -> bool {
    let refs_counter = self.value.assume_init_ref();
    let mut refs = refs_counter.refs.load(Ordering::Relaxed);

    loop {
      // If the reference count is zero, then the node has already been
      // queued for deletion. Incrementing it again could lead to a
      // double-free.
      if refs == 0 {
        return false;
      }

      // If all bits in the reference count are ones, we're about to overflow it.
      let new_refs = refs
        .checked_add(1)
        .expect("RawNode reference count overflow");

      // Try incrementing the count.
      match refs_counter.refs.compare_exchange_weak(
        refs,
        new_refs,
        Ordering::Relaxed,
        Ordering::Relaxed,
      ) {
        Ok(_) => return true,
        Err(current) => refs = current,
      }
    }
  }

  /// Decrements the reference count of a node, destroying it if the count becomes zero.
  #[inline]
  unsafe fn decrement(&self, guard: &Guard) {
    if self
      .value
      .assume_init_ref()
      .refs
      .fetch_sub(1, Ordering::Release)
      == 1
    {
      fence(Ordering::Acquire);
      unsafe { guard.defer_unchecked(move || Self::finalize(self)) }
    }
  }

  /// Decrements the reference count of a node, pinning the thread and destroying the node
  /// if the count become zero.
  #[inline]
  unsafe fn decrement_with_pin<F>(&self, parent: &RawLinkedList<T>, pin: F)
  where
    F: FnOnce() -> Guard,
  {
    if self
      .value
      .assume_init_ref()
      .refs
      .fetch_sub(1, Ordering::Release)
      == 1
    {
      fence(Ordering::Acquire);
      let guard = &pin();
      parent.checkguard(guard);
      unsafe { guard.defer_unchecked(move || Self::finalize(self)) }
    }
  }

  /// Drops the key and value of a node, then deallocates it.
  #[cold]
  unsafe fn finalize(ptr: *const Self) {
    let ptr = ptr as *mut Self;

    unsafe {
      if mem::needs_drop::<T>() {
        // SAFETY: the value is initialized
        ptr::drop_in_place(&mut (*ptr).value.assume_init_mut().value);
      }

      // Finally, deallocate the memory occupied by the node.
      let _ = Box::from_raw(ptr);
    }
  }
}

/// A node in the raw linked list
pub struct Node<'a, 'g, T> {
  parent: &'a RawLinkedList<T>,
  node: &'g RawNode<T>,
  guard: &'g Guard,
}

impl<'a: 'g, 'g, T> Node<'a, 'g, T> {
  /// Returns a reference to the value of the node
  pub const fn value(&self) -> &T {
    unsafe { &self.node.value.assume_init_ref().value }
  }

  /// Returns a reference to the parent `RawLinkedList`
  pub fn linked_list(&self) -> &'a RawLinkedList<T> {
    self.parent
  }

  /// Moves to the next entry in the linked list.
  pub fn move_next(&mut self) -> bool {
    match self.next() {
      None => false,
      Some(n) => {
        *self = n;
        true
      }
    }
  }

  /// Returns the next node in the linked list.
  pub fn next(&self) -> Option<Node<'a, 'g, T>> {
    let backoff = Backoff::new();
    loop {
      let next = self.node.next.load_consume(self.guard);

      if next.is_null() {
        return None;
      }

      if next.tag() == 1 {
        backoff.snooze();
        continue;
      }

      return Some(Node {
        parent: self.parent,
        node: unsafe { next.deref() },
        guard: self.guard,
      });
    }
  }

  /// Attempts to pin the node with a reference count, ensuring that it
  /// remains accessible even after the `Guard` is dropped.
  ///
  /// This method may return `None` if the reference count is already 0 and
  /// the node has been queued for deletion.
  pub fn pin(&self) -> Option<RefNode<'a, T>> {
    unsafe { RefNode::try_acquire(self.parent, self.node) }
  }
}

/// A reference-counted entry in a linked list.
///
/// You *must* call `release` to free this type, otherwise the node will be
/// leaked. This is because releasing the entry requires a `Guard`.
pub struct RefNode<'a, T> {
  parent: &'a RawLinkedList<T>,
  node: &'a RawNode<T>,
}

impl<'a, T> RefNode<'a, T> {
  /// Returns a reference to the parent `RawLinkedList`
  #[inline]
  pub const fn linked_list(&self) -> &'a RawLinkedList<T> {
    self.parent
  }

  /// Returns a reference to the value of the node
  #[inline]
  pub const fn value(&self) -> &T {
    unsafe { &self.node.value.assume_init_ref().value }
  }

  /// Releases the reference on the entry.
  pub fn release(self, guard: &Guard) {
    self.parent.checkguard(guard);
    unsafe { self.node.decrement(guard) }
  }

  /// Releases the reference of the entry, pinning the thread only when
  /// the reference count of the node becomes 0.
  pub fn release_with_pin<F>(self, pin: F)
  where
    F: FnOnce() -> Guard,
  {
    unsafe { self.node.decrement_with_pin(self.parent, pin) }
  }

  /// Tries to create a new `RefNode` by incrementing the reference count of
  /// a node.
  unsafe fn try_acquire(parent: &'a RawLinkedList<T>, node: &RawNode<T>) -> Option<Self> {
    if unsafe { node.try_increment() } {
      Some(Self {
        parent,

        // We re-bind the lifetime of the node here to that of the linked
        // list since we now hold a reference to it.
        node: unsafe { &*(node as *const _) },
      })
    } else {
      None
    }
  }
}

impl<T> Clone for RefNode<'_, T> {
  fn clone(&self) -> Self {
    unsafe {
      // Incrementing will always succeed since we're already holding a reference to the node.
      RawNode::try_increment(self.node);
    }
    Self {
      parent: self.parent,
      node: self.node,
    }
  }
}

impl<T> fmt::Debug for RefNode<'_, T>
where
  T: fmt::Debug,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("RefNode").field(self.value()).finish()
  }
}

impl<'a, T> RefNode<'a, T> {
  /// Moves to the next entry in the linked list.
  pub fn move_next(&mut self, guard: &Guard) -> bool {
    match self.next(guard) {
      None => false,
      Some(e) => {
        mem::replace(self, e).release(guard);
        true
      }
    }
  }

  /// Returns the next entry in the linked list.
  pub fn next(&self, guard: &Guard) -> Option<RefNode<'a, T>> {
    self.parent.checkguard(guard);

    unsafe {
      let backoff = Backoff::new();
      loop {
        let next = self.node.next.load_consume(guard);

        if next.is_null() {
          return None;
        }

        if next.tag() == 1 {
          backoff.snooze();
          continue;
        }

        let n = Node {
          parent: self.parent,
          node: next.deref(),
          guard,
        };

        if let Some(e) = RefNode::try_acquire(self.parent, n.node) {
          return Some(e);
        }
      }
    }
  }
}

/// A lock-free linked list.
///
/// The linked list implementation is based on the [A Pragmatic Implementation of Non-Blocking Linked-Lists](https://www.cl.cam.ac.uk/research/srg/netos/papers/2001-caslists.pdf).
pub struct RawLinkedList<T> {
  /// A sentinel node that is always present in the linked list
  head: RawNode<T>,
  /// The `Collector` associated with this linked list.
  collector: Collector,
  len: AtomicUsize,
}

#[cfg(feature = "std")]
impl<T> Default for RawLinkedList<T> {
  #[inline]
  fn default() -> Self {
    Self::new(crossbeam_epoch::default_collector().clone())
  }
}

impl<T> RawLinkedList<T> {
  /// Create a new empty linked list
  #[inline]
  pub const fn new(collector: Collector) -> Self {
    Self {
      head: RawNode::<T>::UNINIT,
      collector,
      len: AtomicUsize::new(0),
    }
  }

  /// Returns the number of elements in the linked list.
  #[inline]
  pub fn len(&self) -> usize {
    self.len.load(Ordering::Acquire)
  }

  /// Returns `true` if the linked list is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.len() == 0
  }

  /// Iterates over the linked list and removes every node.
  pub fn clear(&self, g: &mut Guard) {
    self.checkguard(g);

    /// Number of steps after which we repin the current thread and unlink removed nodes.
    const BATCH_SIZE: usize = 100;

    let backoff = Backoff::new();
    loop {
      {
        for _ in 0..BATCH_SIZE {
          // get the next node of head
          let next = self.head.next.load_consume(g);
          // tag is 1, this node is being removed
          if next.tag() == 1 {
            // wait other thread to make progress
            backoff.snooze();
            continue;
          }

          // if next is null, the list is empty
          if next.is_null() {
            return;
          }

          let next_next = unsafe { next.deref().next.load_consume(g) };

          // tag is 1, the next next node is being removed
          if next_next.tag() == 1 {
            // wait other thread to make progress
            backoff.snooze();
            continue;
          }

          // mark the next node as being removed
          let removed_next = next.with_tag(1);
          if self
            .head
            .next
            .compare_exchange_weak(next, removed_next, Ordering::AcqRel, Ordering::Relaxed, g)
            .is_err()
          {
            // other thread operated the next node, wait other thread to make progress
            backoff.snooze();
            continue;
          }

          // we have marked the next node as being removed, now, let's try to make the head.next
          // point to the next next node

          // CAS the head's next points to the next next node
          if self
            .head
            .next
            .compare_exchange_weak(
              removed_next,
              next_next,
              Ordering::AcqRel,
              Ordering::Relaxed,
              g,
            )
            .is_ok()
          {
            // SAFETY: next is not null
            self.len.fetch_sub(1, Ordering::Relaxed);
          }
        }
      }

      // Repin the current thread because we don't want to keep it pinned in the same
      // epoch for a too long time.
      g.repin();
    }
  }

  /// Return the first element of the linked list.
  pub fn front(&self, g: &Guard) -> Option<RefNode<'_, T>> {
    let backoff = Backoff::new();
    unsafe {
      loop {
        let node = self.head.next.load_consume(g);
        // if head is being removed, wait other thread to make progress
        if node.tag() == 1 {
          backoff.snooze();
          continue;
        }

        if node.is_null() {
          return None;
        }

        let n = Node {
          parent: self,
          node: node.deref(),
          guard: g,
        };

        if let Some(n) = RefNode::try_acquire(self, n.node) {
          return Some(n);
        }
      }
    }
  }

  /// Push a value to the front of the linked list and return the node that was pushed.
  pub fn push(&self, value: T, g: &Guard) -> RefNode<'_, T> {
    self.checkguard(g);
    let backoff = Backoff::new();
    unsafe {
      // Rebind the guard to the lifetime of self. This is a bit of a
      // hack but it allows us to return references that are not bound to
      // the lifetime of the guard.
      let g = &*(g as *const _);

      // The reference count of the new node is 2, one for the node in the linked list, and one for the
      // return RefNode.
      let new_node = Owned::new(RawNode::new(value, 2))
        .with_tag(0)
        .into_shared(g);

      // +----------------+     +------------+     +----------------+
      // |      head      |     |    node    |     |      next      |
      // |      next      |---->|            |     |                |
      // |                |     |    next    |---->|                |
      // +----------------+     +------------+     +----------------+
      //
      // 1. Initialize node's next to point to next.
      // 2. CAS head's next to repoint from next to node.
      loop {
        // get the next node of head
        let next = self.head.next.load_consume(g);
        let tag = next.tag();
        // tag is 1, this node is being removed
        if tag == 1 {
          // wait other thread to make progress
          backoff.snooze();
          continue;
        }

        // Relaxed is enough because no other thread is accessing the new node
        new_node.deref().next.store(next, Ordering::Relaxed);

        // CAS the head's next to the new node
        if self
          .head
          .next
          .compare_exchange_weak(next, new_node, Ordering::AcqRel, Ordering::Relaxed, g)
          .is_err()
        {
          backoff.spin();
          continue;
        }

        self.len.fetch_add(1, Ordering::Relaxed);
        return RefNode {
          parent: self,
          node: new_node.deref(),
        };
      }
    }
  }

  /// Pop a value from the front of the linked list
  ///
  /// This operation is `O(1)`.
  pub fn pop<'a: 'g, 'g>(&'a self, g: &'g Guard) -> Option<RefNode<'a, T>> {
    self.checkguard(g);

    let backoff = Backoff::new();
    unsafe {
      loop {
        // get the next node of head
        let next = self.head.next.load_consume(g);
        // tag is 1, this node is being removed
        if next.tag() == 1 {
          // wait other thread to make progress
          backoff.snooze();
          continue;
        }

        // if next is null, the list is empty
        if next.is_null() {
          return None;
        }

        // mark the next node as being removed
        let removed_next = next.with_tag(1);
        if self
          .head
          .next
          .compare_exchange_weak(next, removed_next, Ordering::AcqRel, Ordering::Relaxed, g)
          .is_err()
        {
          // other thread operated the next node, wait other thread to make progress
          backoff.snooze();
          continue;
        }

        // Revalidate next after marking it as removed
        let reloaded_next = self.head.next.load_consume(g);
        if reloaded_next != removed_next {
          backoff.snooze();
          continue;
        }

        let next_next = next.deref().next.load_consume(g);
        if next_next.tag() == 1 {
          // wait other thread to make progress
          backoff.snooze();
          continue;
        }

        // we have marked the next node as being removed, now, let's try to make the head.next
        // point to the next next node

        // CAS the head's next points to the next next node
        if self
          .head
          .next
          .compare_exchange_weak(
            removed_next,
            next_next,
            Ordering::AcqRel,
            Ordering::Relaxed,
            g,
          )
          .is_ok()
        {
          self.len.fetch_sub(1, Ordering::Relaxed);
          let node = Node {
            parent: self,
            node: removed_next.deref(),
            guard: g,
          };

          if let Some(nr) = node.pin() {
            return Some(nr);
          }
        }
        backoff.spin();
      }
    }
  }

  #[inline]
  fn checkguard(&self, guard: &Guard) {
    if let Some(c) = guard.collector() {
      assert!(c == &self.collector);
    }
  }
}

impl<T: PartialEq> RawLinkedList<T> {
  /// Returns `true` if the linked list contains the specified value.
  pub fn contains(&self, value: &T, guard: &Guard) -> bool {
    self.checkguard(guard);

    let mut current = self.head.next.load_consume(guard);
    let backoff = Backoff::new();

    unsafe {
      loop {
        // if the next node of head is null, the list is empty
        if current.is_null() {
          return false;
        }

        if current.tag() == 1 {
          backoff.snooze();
          current = self.head.next.load_consume(guard);
          continue;
        }

        let node = current.deref();
        if &node.value.assume_init_ref().value == value {
          return true;
        }

        current = node.next.load_consume(guard);
      }
    }
  }
}

impl<T> Drop for RawLinkedList<T> {
  fn drop(&mut self) {
    unsafe {
      let mut node = self
        .head
        .next
        .load(Ordering::Relaxed, crossbeam_epoch::unprotected());

      // Iterate through the whole linked list and destroy every node.
      loop {
        // list is empty
        if node.is_null() {
          return;
        }

        let current = node.deref();
        let next = current
          .next
          .load(Ordering::Relaxed, crossbeam_epoch::unprotected());

        RawNode::finalize(current);

        if next.is_null() {
          break;
        }

        node = next;
      }
    }
  }
}
