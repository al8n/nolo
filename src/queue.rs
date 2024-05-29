use core::{fmt, mem::ManuallyDrop, ptr};

use super::*;

/// [`RawLinkedList`] implementation.
pub mod raw;

/// A lock-free unbounded queue based on linked list.
pub struct Queue<T> {
  raw: raw::RawLinkedList<T>,
}

#[cfg(feature = "std")]
impl<T> Default for Queue<T> {
  #[inline]
  fn default() -> Self {
    Self::new()
  }
}

impl<T> Queue<T> {
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

  /// Peeks the first element in queue.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::queue::Queue;
  ///
  /// let q: Queue<i32> = Queue::new();
  ///
  /// q.push(42);
  /// q.push(84);
  ///
  /// let node = q.peek().unwrap();
  /// assert_eq!(*node.value(), 42);
  /// ```
  #[inline]
  pub fn peek(&self) -> Option<Node<'_, T>> {
    let guard = &epoch::pin();
    self.raw.back(guard).map(Node::new)
  }

  /// Pushes a value to the front of the linked list.
  ///
  /// This function returns an [`Node`] which
  /// can be used to access the inserted key's associated value.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::queue::Queue;
  ///
  /// let q: Queue<i32> = Queue::new();
  ///
  /// let node = q.push(42);
  /// assert_eq!(*node.value(), 42);
  ///
  /// let node = q.push(84);
  /// assert_eq!(*node.value(), 84);
  /// ```
  pub fn push(&self, elem: T) -> Node<'_, T> {
    let guard = &epoch::pin();
    Node::new(self.raw.push_front(elem, guard))
  }

  /// Pops a value from the front of the queue.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::queue::Queue;
  ///
  /// let q: Queue<i32> = Queue::new();
  ///
  /// q.push(42);
  /// q.push(84);
  ///
  /// assert_eq!(q.pop().map(|node| *node.value()), Some(42));
  /// assert_eq!(q.pop().map(|node| *node.value()), Some(84));
  /// assert_eq!(q.pop().map(|node| *node.value()), None);
  /// ```
  pub fn pop(&self) -> Option<Node<'_, T>> {
    let guard = &epoch::pin();
    self.raw.pop_back(guard).map(Node::new)
  }

  /// Returns `true` if the queue is empty.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::queue::Queue;
  ///
  /// let q: Queue<i32> = Queue::new();
  ///
  /// assert!(q.is_empty());
  ///
  /// q.push(42);
  ///
  /// assert!(!q.is_empty());
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.raw.is_empty()
  }

  /// Returns the number of elements in the queue.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::queue::Queue;
  ///
  /// let q: Queue<i32> = Queue::new();
  ///
  /// assert_eq!(q.len(), 0);
  ///
  /// q.push(42);
  ///
  /// assert_eq!(q.len(), 1);
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn test_queue() {
    let q: Queue<i32> = Queue::new();

    q.push(42);
    q.push(84);

    assert!(!q.is_empty());
    assert_eq!(q.len(), 2);

    let node = q.peek().unwrap();
    assert_eq!(*node.value(), 42);

    let node = q.pop().unwrap();
    assert_eq!(*node.value(), 42);

    let node = q.pop().unwrap();
    assert_eq!(*node.value(), 84);

    // assert!(q.is_empty());
    // assert_eq!(q.len(), 0);
  }
}
