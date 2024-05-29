use core::{fmt, mem::ManuallyDrop, ptr};

use super::*;

/// [`RawLinkedList`] implementation.
pub mod raw;

/// A lock-free linked list.
///
/// The linked list implementation is based on the [A Pragmatic Implementation of Non-Blocking Linked-Lists](https://www.cl.cam.ac.uk/research/srg/netos/papers/2001-caslists.pdf).
#[repr(transparent)]
pub struct LinkedList<T> {
  raw: raw::RawLinkedList<T>,
}

#[cfg(feature = "std")]
impl<T> Default for LinkedList<T> {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl<T> LinkedList<T> {
  /// Creates a new empty linked list.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::linked_list::LinkedList;
  ///
  /// let list: LinkedList<i32> = LinkedList::new();
  /// ```
  #[cfg(feature = "std")]
  #[inline]
  pub fn new() -> Self {
    Self {
      raw: raw::RawLinkedList::new(crossbeam_epoch::default_collector().clone()),
    }
  }

  /// Creates a new empty linked list with the given garbage collector.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::{linked_list::LinkedList, default_collector};
  ///
  /// let list: LinkedList<i32> = LinkedList::with_collector(default_collector().clone());
  /// ```
  #[inline]
  pub fn with_collector(collector: crossbeam_epoch::Collector) -> Self {
    Self {
      raw: raw::RawLinkedList::new(collector),
    }
  }

  /// Returns a reference to the front of the linked list.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::linked_list::LinkedList;
  ///
  /// let list: LinkedList<i32> = LinkedList::new();
  ///
  /// list.push(42);
  /// list.push(84);
  ///
  /// let node = list.front().unwrap();
  /// assert_eq!(*node.value(), 84);
  /// ```
  #[inline]
  pub fn front(&self) -> Option<Node<'_, T>> {
    let guard = &epoch::pin();
    self.raw.front(guard).map(Node::new)
  }

  /// Pushes a value to the front of the linked list.
  ///
  /// This function returns an [`Node`] which
  /// can be used to access the inserted key's associated value.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::linked_list::LinkedList;
  ///
  /// let list: LinkedList<i32> = LinkedList::new();
  ///
  /// let node = list.push(42);
  /// assert_eq!(*node.value(), 42);
  ///
  /// let node = list.push(84);
  /// assert_eq!(*node.value(), 84);
  /// ```
  pub fn push(&self, elem: T) -> Node<'_, T> {
    let guard = &epoch::pin();
    Node::new(self.raw.push(elem, guard))
  }

  /// Pops a value from the front of the linked list.
  ///
  /// This operation is `O(1)`.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::linked_list::LinkedList;
  ///
  /// let list: LinkedList<i32> = LinkedList::new();
  ///
  /// list.push(42);
  /// list.push(84);
  ///
  /// assert_eq!(list.pop().map(|node| *node.value()), Some(84));
  /// assert_eq!(list.pop().map(|node| *node.value()), Some(42));
  /// assert_eq!(list.pop().map(|node| *node.value()), None);
  /// ```
  pub fn pop(&self) -> Option<Node<'_, T>> {
    let guard = &epoch::pin();
    self.raw.pop(guard).map(Node::new)
  }

  /// Returns `true` if the list is empty.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::linked_list::LinkedList;
  ///
  /// let list: LinkedList<i32> = LinkedList::new();
  ///
  /// assert!(list.is_empty());
  ///
  /// list.push(42);
  ///
  /// assert!(!list.is_empty());
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.raw.is_empty()
  }

  /// Returns the number of elements in the list.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::linked_list::LinkedList;
  ///
  /// let list: LinkedList<i32> = LinkedList::new();
  ///
  /// assert_eq!(list.len(), 0);
  ///
  /// list.push(42);
  ///
  /// assert_eq!(list.len(), 1);
  /// ```
  #[inline]
  pub fn len(&self) -> usize {
    self.raw.len()
  }
}

/// A reference-counted entry in a map.
pub struct Node<'a, T> {
  inner: ManuallyDrop<raw::RefNode<'a, T>>,
}

impl<'a, T> Node<'a, T> {
  fn new(inner: raw::RefNode<'a, T>) -> Self {
    Self {
      inner: ManuallyDrop::new(inner),
    }
  }

  /// Returns a reference to the value.
  #[inline]
  pub fn value(&self) -> &T {
    self.inner.value()
  }
}

impl<T> Drop for Node<'_, T> {
  fn drop(&mut self) {
    unsafe {
      ManuallyDrop::into_inner(ptr::read(&self.inner)).release_with_pin(epoch::pin);
    }
  }
}

impl<'a, T> Node<'a, T> {
  /// Moves to the next entry in the map.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::linked_list::LinkedList;
  ///
  /// let list: LinkedList<i32> = LinkedList::new();
  ///
  /// let node = list.push(42);
  /// assert_eq!(*node.value(), 42);
  ///
  /// let node = list.push(84);
  /// assert_eq!(*node.value(), 84);
  ///
  /// let mut first = list.front();
  /// assert_eq!(*first.value(), 84);
  ///
  /// assert!(first.move_next());
  /// assert_eq!(*first.value(), 42);
  /// ```
  #[inline]
  pub fn move_next(&mut self) -> bool {
    let guard = &epoch::pin();
    self.inner.move_next(guard)
  }

  /// Returns the next entry in the map.
  #[inline]
  pub fn next(&self) -> Option<Node<'a, T>> {
    let guard = &epoch::pin();
    self.inner.next(guard).map(Node::new)
  }
}

impl<T> Clone for Node<'_, T> {
  fn clone(&self) -> Self {
    Self {
      inner: self.inner.clone(),
    }
  }
}

impl<T> fmt::Debug for Node<'_, T>
where
  T: fmt::Debug,
{
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("Node").field(self.value()).finish()
  }
}
