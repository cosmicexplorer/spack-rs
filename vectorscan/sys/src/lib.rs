/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

/* Warn for missing docs in general, and hard require crate-level docs. */
// #![warn(missing_docs)]
#![deny(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
/* Generate docs.rs info for feature switches. */
#![cfg_attr(docsrs, feature(doc_cfg))]

#[allow(unused, improper_ctypes, clippy::all)]
mod bindings {
  include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}
pub use bindings::root as hs;
