use crate::linked_list::{LinkedList, Node};

/// A lock-free unbounded stack based on linked list.
#[derive(Default)]
#[repr(transparent)]
pub struct Stack<T>(LinkedList<T>);

impl<T> Stack<T> {
  /// Creates a new empty stack.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::stack::Stack;
  ///
  /// let stack: Stack<i32> = Stack::new();
  /// ```
  #[cfg(feature = "std")]
  #[inline]
  pub fn new() -> Self {
    Self(LinkedList::new())
  }

  /// Creates a new empty stack with the given garbage collector.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::{stack::Stack, default_collector};
  ///
  /// let stack: Stack<i32> = Stack::with_collector(default_collector().clone());
  /// ```
  #[inline]
  pub fn with_collector(collector: crossbeam_epoch::Collector) -> Self {
    Self(LinkedList::with_collector(collector))
  }

  /// Returns the number of elements in the stack.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::stack::Stack;
  ///
  /// let stack: Stack<i32> = Stack::new();
  ///
  /// assert_eq!(stack.len(), 0);
  /// stack.push(42);
  ///
  /// assert_eq!(stack.len(), 1);
  /// ```
  #[inline]
  pub fn len(&self) -> usize {
    self.0.len()
  }

  /// Returns `true` if the stack is empty.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::stack::Stack;
  ///
  /// let stack: Stack<i32> = Stack::new();
  ///
  /// assert!(stack.is_empty());
  ///
  /// stack.push(42);
  ///
  /// assert!(!stack.is_empty());
  /// ```
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.0.is_empty()
  }

  /// Pushes an element to the top of the stack.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::stack::Stack;
  ///
  /// let stack: Stack<i32> = Stack::new();
  /// stack.push(42);
  /// ```
  #[inline]
  pub fn push(&self, data: T) -> Node<'_, T> {
    self.0.push(data)
  }

  /// Pops an element from the top of the stack.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::stack::Stack;
  ///
  /// let stack: Stack<i32> = Stack::new();
  /// stack.push(42);
  /// assert_eq!(stack.pop(), Some(42));
  /// ```
  #[inline]
  pub fn pop(&self) -> Option<Node<'_, T>> {
    self.0.pop()
  }

  /// Peeks the top element in stack.
  ///
  /// # Examples
  ///
  /// ```rust
  /// use unlockism::stack::Stack;
  ///
  /// let stack: Stack<i32> = Stack::new();
  /// stack.push(42);
  /// assert_eq!(stack.peek(), Some(&42));
  /// ```
  #[inline]
  pub fn peek(&self) -> Option<Node<'_, T>> {
    self.0.front()
  }
}
