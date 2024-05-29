//! A template for creating Rust open-source repo on GitHub
#![cfg_attr(not(any(feature = "std", test)), no_std)]
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, allow(unused_attributes))]
#![deny(missing_docs)]
#![allow(unexpected_cfgs)]

#[cfg(not(feature = "std"))]
extern crate alloc as std;

#[cfg(feature = "std")]
extern crate std;

#[cfg(feature = "std")]
pub use crossbeam_epoch::{default_collector, is_pinned, pin};

use crossbeam_epoch as epoch;

/// Lock free doubly linked list, if you only need a singly linked list, see [`linked_list`] instead.
#[cfg(any(feature = "alloc", feature = "std"))]
pub mod doubly_linked_list;

/// Lock free linked list, if you need a doubly linked list, see [`doubly_linked_list`] instead.
///
/// The linked list implementation is based on the [A Pragmatic Implementation of Non-Blocking Linked-Lists](https://www.cl.cam.ac.uk/research/srg/netos/papers/2001-caslists.pdf).
#[cfg(any(feature = "alloc", feature = "std"))]
pub mod linked_list;

/// A lock-free unbounded queue based on doubly linked list.
#[cfg(any(feature = "alloc", feature = "std"))]
pub mod queue;

/// A lock-free unbounded stack based on linked list.
#[cfg(any(feature = "alloc", feature = "std"))]
pub mod stack;

pub(crate) mod utils;
use utils::*;

mod sync {
  #[cfg(loom)]
  pub(crate) use loom::sync::{atomic::*, *};

  #[cfg(not(loom))]
  pub(crate) use std::sync::{atomic::*, *};
}
