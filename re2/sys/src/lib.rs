/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

#[allow(unused, improper_ctypes, clippy::all)]
mod bindings {
  include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}
pub use bindings::root::{re2, re2_c_bindings as re2_c};
