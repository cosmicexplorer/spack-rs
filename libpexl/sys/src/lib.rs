/* Copyright 2024 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

#[allow(
  unused,
  improper_ctypes,
  clippy::all,
  non_camel_case_types,
  non_upper_case_globals
)]
mod bindings {
  include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}
pub use bindings::*;
