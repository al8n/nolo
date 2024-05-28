use core::{
  mem::{self, MaybeUninit},
  ptr,
};

use crossbeam_epoch::{Atomic, Collector, Guard, Owned};
use crossbeam_utils::Backoff;

use super::sync::*;

struct Ref<T> {
  value: T,
  refs: AtomicUsize,
}

impl<T> Ref<T> {
  #[inline]
  fn new(value: T) -> Self {
    Self {
      value,
      refs: AtomicUsize::new(1),
    }
  }
}

struct RawNode<T> {
  /// The value of the node
  value: MaybeUninit<Ref<T>>,

  /// The next node in the linked list
  next: Atomic<RawNode<T>>,
  /// The previous node in the linked list
  prev: Atomic<RawNode<T>>,
}

impl<T> RawNode<T> {
  const UNINIT: Self = Self {
    value: MaybeUninit::uninit(),
    next: Atomic::null(),
    prev: Atomic::null(),
  };

  /// Create a new node
  #[inline]
  fn new(value: T) -> Self {
    RawNode {
      value: MaybeUninit::new(Ref::new(value)),
      next: Atomic::null(),
      prev: Atomic::null(),
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
      parent.check_guard(guard);
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
  _guard: &'g Guard,
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

  /// Attempts to pin the node with a reference count, ensuring that it
  /// remains accessible even after the `Guard` is dropped.
  ///
  /// This method may return `None` if the reference count is already 0 and
  /// the node has been queued for deletion.
  pub fn pin(&self) -> Option<RefNode<'a, T>> {
    unsafe { RefNode::try_acquire(self.parent, self.node) }
  }
}

/// A reference-counted entry in a skip list.
///
/// You *must* call `release` to free this type, otherwise the node will be
/// leaked. This is because releasing the entry requires a `Guard`.
pub struct RefNode<'a, T> {
  parent: &'a RawLinkedList<T>,
  node: &'a RawNode<T>,
}

impl<'a, T> RefNode<'a, T> {
  /// Returns a reference to the parent `RawLinkedList`
  pub fn linked_list(&self) -> &'a RawLinkedList<T> {
    self.parent
  }

  /// Releases the reference on the entry.
  pub fn release(self, guard: &Guard) {
    self.parent.check_guard(guard);
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

  /// Tries to create a new `RefEntry` by incrementing the reference count of
  /// a node.
  unsafe fn try_acquire(parent: &'a RawLinkedList<T>, node: &RawNode<T>) -> Option<Self> {
    if unsafe { node.try_increment() } {
      Some(Self {
        parent,

        // We re-bind the lifetime of the node here to that of the skip
        // list since we now hold a reference to it.
        node: unsafe { &*(node as *const _) },
      })
    } else {
      None
    }
  }
}

/// A lock-free linked list.
pub struct RawLinkedList<T> {
  /// A sentinel node that is always present in the linked list
  head: RawNode<T>,
  tail: RawNode<T>,
  /// The `Collector` associated with this skip list.
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
      tail: RawNode::<T>::UNINIT,
      collector,
      len: AtomicUsize::new(0),
    }
  }

  /// Return the first element of the linked list.
  pub fn front<'a, 'g>(&'a self, g: &'g Guard) -> Option<Node<'a, 'g, T>> {
    let backoff = Backoff::new();
    unsafe {
      loop {
        let head_ptr = self.head.next.load_consume(g);
        // if head is being removed, wait other thread to make progress
        if head_ptr.tag() == 1 {
          backoff.snooze();
          continue;
        }

        let head = head_ptr.deref();
        // if the next is tail, the list is empty
        if head.value.as_ptr().is_null() {
          return None;
        }

        return Some(Node {
          parent: self,
          node: head,
          _guard: g,
        });
      }
    }
  }

  /// Return the last element of the linked list.
  pub fn back<'a, 'g>(&'a self, g: &'g Guard) -> Option<Node<'a, 'g, T>> {
    let backoff = Backoff::new();
    unsafe {
      loop {
        let tail_ptr = self.tail.prev.load_consume(g);
        // if tail is being removed, wait other thread to make progress
        if tail_ptr.tag() == 1 {
          backoff.snooze();
          continue;
        }

        let tail = tail_ptr.deref();

        // if the prev is head, the list is empty
        if tail.value.as_ptr().is_null() {
          return None;
        }

        return Some(Node {
          parent: self,
          node: tail,
          _guard: g,
        });
      }
    }
  }

  /// Push a value to the front of the linked list and return the node that was pushed.
  pub fn push_front<'a: 'g, 'g>(&'a self, value: T, g: &'g Guard) -> Node<'a, 'g, T> {
    self.check_guard(g);
    let backoff = Backoff::new();
    let mut new_node = Owned::new(RawNode::new(value)).with_tag(0).into_shared(g);

    unsafe {
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
        match self.head.next.compare_exchange_weak(
          next,
          new_node,
          Ordering::AcqRel,
          Ordering::Relaxed,
          g,
        ) {
          Ok(_) => {
            self.len.fetch_add(1, Ordering::Relaxed);
            return Node {
              parent: self,
              node: new_node.deref(),
              _guard: g,
            };
          }
          Err(e) => {
            new_node = e.new;
            backoff.spin();
          }
        }
      }
    }
  }

  /// Push a value to the back of the linked list, and return the node that was pushed.
  pub fn push_back<'a: 'g, 'g>(&'a self, value: T, g: &'g Guard) -> Node<'a, 'g, T> {
    self.check_guard(g);

    let backoff = Backoff::new();
    let mut new_node = Owned::new(RawNode::new(value)).with_tag(0).into_shared(g);

    unsafe {
      loop {
        // get the prev node of tail
        let prev = self.tail.prev.load_consume(g);
        // tag is 1, this node is being removed
        if prev.tag() == 1 {
          // wait other thread to make progress
          backoff.snooze();
          continue;
        }

        // Relaxed is enough because no other thread is accessing the new node
        new_node.deref().prev.store(prev, Ordering::Relaxed);

        // CAS the tail's prev to the new node
        match self.tail.prev.compare_exchange_weak(
          prev,
          new_node,
          Ordering::AcqRel,
          Ordering::Relaxed,
          g,
        ) {
          Ok(_) => {
            self.len.fetch_add(1, Ordering::Relaxed);
            return Node {
              parent: self,
              node: new_node.deref(),
              _guard: g,
            };
          }
          Err(e) => {
            new_node = e.new;
            backoff.spin();
          }
        }
      }
    }
  }

  /// Pop a value from the front of the linked list
  pub fn pop_front<'a: 'g, 'g>(&'a self, g: &'g Guard) -> Option<RefNode<'a, T>> {
    self.check_guard(g);

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

        let next_next = next.deref().next.load_consume(g);

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
          let node = Node {
            parent: self,
            node: removed_next.deref(),
            _guard: g,
          };

          if let Some(nr) = node.pin() {
            return Some(nr);
          }
        }
        backoff.spin();
      }
    }
  }

  /// Pop a value from the back of the linked list
  pub fn pop_back<'a: 'g, 'g>(&'a self, g: &'g Guard) -> Option<RefNode<'a, T>> {
    self.check_guard(g);

    let backoff = Backoff::new();
    unsafe {
      loop {
        // get the prev node of tail
        let prev = self.tail.prev.load_consume(g);
        // tag is 1, this node is being removed
        if prev.tag() == 1 {
          // wait other thread to make progress
          backoff.snooze();
          continue;
        }

        // if prev is null, the list is empty
        if prev.is_null() {
          return None;
        }

        let prev_prev = prev.deref().prev.load_consume(g);

        // tag is 1, the prev prev node is being removed
        if prev_prev.tag() == 1 {
          // wait other thread to make progress
          backoff.snooze();
          continue;
        }

        // mark the prev node as being removed
        let removed_prev = prev.with_tag(1);
        if self
          .tail
          .prev
          .compare_exchange_weak(prev, removed_prev, Ordering::AcqRel, Ordering::Relaxed, g)
          .is_err()
        {
          // other thread operated the prev node, wait other thread to make progress
          backoff.snooze();
          continue;
        }

        // we have marked the prev node as being removed, now, let's try to make the tail.prev
        // point to the prev prev node

        // CAS the tail's prev points to the prev prev node
        if self
          .tail
          .prev
          .compare_exchange_weak(
            removed_prev,
            prev_prev,
            Ordering::AcqRel,
            Ordering::Relaxed,
            g,
          )
          .is_ok()
        {
          // SAFETY: prev is not null
          self.len.fetch_sub(1, Ordering::Relaxed);
          let node = Node {
            parent: self,
            node: removed_prev.deref(),
            _guard: g,
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
  fn check_guard(&self, guard: &Guard) {
    if let Some(c) = guard.collector() {
      assert!(c == &self.collector);
    }
  }
}
