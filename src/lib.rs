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

/// Lock free linked list
#[cfg(any(feature = "alloc", feature = "std"))]
pub mod linked_list;

pub(crate) mod utils;
use utils::*;

mod sync {
  #[cfg(loom)]
  pub(crate) use loom::sync::{atomic::*, *};

  #[cfg(not(loom))]
  pub(crate) use std::sync::{atomic::*, *};
}
