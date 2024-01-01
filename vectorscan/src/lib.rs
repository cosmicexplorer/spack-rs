/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Wrapper for the vectorscan C++ regex library.
//!
//! *TODO: describe feature flags!*
//!
//! **FIXME: describe any outstanding forks, but also make PRs to include
//! those!**

/* Warn for missing docs in general, and hard require crate-level docs. */
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
/* Generate docs.rs info for feature switches. */
#![cfg_attr(docsrs, feature(doc_cfg))]

pub(crate) use vectorscan_sys::hs;

#[cfg(feature = "alloc")]
#[cfg_attr(docsrs, doc(cfg(feature = "alloc")))]
pub mod alloc;
pub mod database;
pub mod error;
#[cfg(feature = "compiler")]
#[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
pub mod expression;
#[cfg(feature = "compiler")]
#[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
pub mod flags;
pub mod matchers;
pub mod sources;
pub mod state;
#[cfg(feature = "stream")]
#[cfg_attr(docsrs, doc(cfg(feature = "stream")))]
pub mod stream;

unsafe fn free_misc(p: *mut u8) {
  let p = p as *mut std::os::raw::c_void;
  cfg_if::cfg_if! {
    if #[cfg(feature = "alloc")] {
      alloc::misc_free_func(p);
    } else {
      libc::free(p);
    }
  }
}

#[cfg(feature = "chimera")]
unsafe fn free_misc_chimera(p: *mut u8) {
  let p = p as *mut std::os::raw::c_void;
  cfg_if::cfg_if! {
    if #[cfg(feature = "alloc")] {
      alloc::chimera::chimera_misc_free_func(p);
    } else {
      libc::free(p);
    }
  }
}

/// Utility function to test the current system architecture.
///
/// Vectorscan requires the Supplemental Streaming SIMD Extensions 3 instruction
/// set. This function can be called on any x86 platform to determine if the
/// system provides the required instruction set.
///
/// This function does not test for more advanced features if Vectorscan has
/// been built for a more specific architecture, for example the AVX2
/// instruction set.
///
/// Returns [`ArchError`](error::VectorscanRuntimeError::ArchError) if system
/// does not support Vectorscan.
///
/// # Dependency on `"compiler"` Feature
/// This method is not available in the `hs_runtime` library for some reason, so
/// it currently cannot be provided without enabling the `"compiler"` feature.
///
///```
/// # fn main() -> Result<(), vectorscan::error::VectorscanRuntimeError> {
/// vectorscan::check_valid_platform()?;
/// # Ok(())
/// # }
/// ```
#[cfg(feature = "compiler")]
#[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
pub fn check_valid_platform() -> Result<(), error::VectorscanRuntimeError> {
  error::VectorscanRuntimeError::from_native(unsafe { hs::hs_valid_platform() })
}

/// Utility function for identifying this release version.
///
/// Returns a string containing the version number of this release build and the
/// date of the build. It is allocated statically, so it does not need to
/// be freed by the caller.
///
///```
/// let v = vectorscan::vectorscan_version().to_str().unwrap();
/// assert!(v.starts_with("5.4.11 "));
/// ```
pub fn vectorscan_version() -> &'static std::ffi::CStr {
  unsafe { std::ffi::CStr::from_ptr(hs::hs_version()) }
}

/// Utility function for identifying this release version.
///
/// Returns a string containing the version number of this release build and the
/// date of the build. It is allocated statically, so it does not need to
/// be freed by the caller.
///
///```
/// let v = vectorscan::chimera_version().to_str().unwrap();
/// assert!(v.starts_with("5.4.11 "));
/// ```
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub fn chimera_version() -> &'static std::ffi::CStr {
  unsafe { std::ffi::CStr::from_ptr(hs::ch_version()) }
}

#[cfg(feature = "async")]
mod async_utils {
  use futures_core::stream::Stream;
  use tokio::sync::mpsc;

  use std::{
    pin::Pin,
    task::{Context, Poll},
  };

  /* Reimplementation of tokio_stream::wrappers::UnboundedReceiverStream. */
  #[derive(Debug)]
  #[repr(transparent)]
  pub struct UnboundedReceiverStream<T>(pub mpsc::UnboundedReceiver<T>);

  impl<T> Stream for UnboundedReceiverStream<T> {
    type Item = T;

    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context) -> Poll<Option<Self::Item>> {
      self.0.poll_recv(cx)
    }
  }
}
