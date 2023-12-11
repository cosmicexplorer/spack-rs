/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Async wrapper for the hyperscan C++ regex library.

/* Warn for missing docs in general, and hard require crate-level docs. */
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
/* Generate docs.rs info for feature switches. */
#![cfg_attr(docsrs, feature(doc_cfg))]

pub(crate) use hyperscan_sys::hs;

#[cfg(feature = "static")]
#[cfg_attr(docsrs, doc(cfg(feature = "static")))]
pub mod alloc;
pub mod database;
pub mod error;
#[cfg(feature = "compile")]
#[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
pub mod expression;
#[cfg(feature = "compile")]
#[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
pub mod flags;
pub mod matchers;
pub mod state;
pub mod stream;

/// Utility function to test the current system architecture.
///
/// Hyperscan requires the Supplemental Streaming SIMD Extensions 3 instruction
/// set. This function can be called on any x86 platform to determine if the
/// system provides the required instruction set.
///
/// This function does not test for more advanced features if Hyperscan has
/// been built for a more specific architecture, for example the AVX2
/// instruction set.
///
/// Returns [`ArchError`](error::HyperscanRuntimeError::ArchError) if system
/// does not support Hyperscan.
///
///```
/// # fn main() -> Result<(), hyperscan::error::HyperscanRuntimeError> {
/// hyperscan::check_valid_platform()?;
/// # Ok(())
/// # }
/// ```
pub fn check_valid_platform() -> Result<(), error::HyperscanRuntimeError> {
  error::HyperscanRuntimeError::from_native(unsafe { hs::hs_valid_platform() })
}

/// Utility function for identifying this release version.
///
/// Returns a string containing the version number of this release build and the
/// date of the build. It is allocated statically, so it does not need to
/// be freed by the caller.
///
///```
/// let v = hyperscan::hyperscan_version().to_str().unwrap();
/// assert!(v.starts_with("5.4.2 2023"));
/// ```
pub fn hyperscan_version() -> &'static std::ffi::CStr {
  unsafe { std::ffi::CStr::from_ptr(hs::hs_version()) }
}

/// Utility function for identifying this release version.
///
/// Returns a string containing the version number of this release build and the
/// date of the build. It is allocated statically, so it does not need to
/// be freed by the caller.
///
///```
/// let v = hyperscan::chimera_version().to_str().unwrap();
/// assert!(v.starts_with("5.4.2 2023"));
/// ```
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub fn chimera_version() -> &'static std::ffi::CStr {
  unsafe { std::ffi::CStr::from_ptr(hs::ch_version()) }
}
