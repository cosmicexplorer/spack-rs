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

mod bindings {
  include!(concat!(env!("OUT_DIR"), "/bindings.rs"));
}
pub(crate) use bindings::root as hs;

pub mod alloc;
pub mod database;
pub mod error;
pub mod expression;
pub mod flags;
pub mod matchers;
pub mod state;
pub mod stream;

///```
/// # fn main() -> Result<(), hyperscan_async::error::HyperscanRuntimeError> {
/// hyperscan_async::check_valid_platform()?;
/// # Ok(())
/// # }
/// ```
pub fn check_valid_platform() -> Result<(), error::HyperscanRuntimeError> {
  error::HyperscanRuntimeError::from_native(unsafe { hs::hs_valid_platform() })
}

///```
/// let v = hyperscan_async::hyperscan_version().to_str().unwrap();
/// assert!(v.starts_with("5.4.2 2023"));
/// ```
pub fn hyperscan_version() -> &'static std::ffi::CStr {
  unsafe { std::ffi::CStr::from_ptr(hs::hs_version()) }
}

///```
/// let v = hyperscan_async::chimera_version().to_str().unwrap();
/// assert!(v.starts_with("5.4.2 2023"));
/// ```
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub fn chimera_version() -> &'static std::ffi::CStr {
  unsafe { std::ffi::CStr::from_ptr(hs::ch_version()) }
}
