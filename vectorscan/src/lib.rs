/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Wrapper for the vectorscan C regex library.
//!
//! # Quirks
//! The [vectorscan] library (originally [hyperscan], from Intel) supports
//! high-performance pattern matching using a subset of PCRE syntax. It was
//! originally written for extremely low-latency network traffic monitoring, so
//! it has some interface quirks that may be unfamiliar:
//! - **[Vectorscan Callback API]:** Matches are "returned" to the user when
//!   vectorscan executes a user-provided C ABI method call, so overlapping
//!   matches and other interactive feedback with the matching engine are much
//!   easier to support compared to a synchronous method call.
//! - **Highly Expressive Pattern Set Matching:** [`expression::ExpressionSet`]
//!   supports the full range of searching and matching operations available to
//!   individual [`expression::Expression`] instances. This is rare: most other
//!   regex engines e.g. do not support finding match offsets, but instead only
//!   which expressions in a set matched.
//! - **[Mutable State and String Searching]:** Vectorscan requires the user to
//!   explicitly provide a "scratch" space with [`state::Scratch`] to each
//!   search method. This state is not very large, but most other regex engines
//!   attempt to present an interface without any mutable state, even if
//!   internally they use constructions like lazy DFAs.
//!
//! [vectorscan]: https://github.com/VectorCamp/vectorscan
//! [hyperscan]: https://github.com/intel/hyperscan
//! [Vectorscan Callback API]: crate::matchers#vectorscan-callback-api
//! [Highly Expressive Pattern Set Matching]: crate::expression
//! [Mutable State and String Searching]: crate::state#mutable-state-and-string-searching
//!
//! # Feature Flags
//! This library uses [`spack-rs`](https://docs.rs/spack-rs) to configure the build of the
//! vectorscan codebase using [`spack`](https://spack.io), so it can be precise about which native
//! dependencies it brings in:
//! - **`"static"` (default):** link against vectorscan statically. Conflicts
//!   with `"dynamic"`.
//! - **`"dynamic"`:** link against vectorscan dynamically. Conflicts with
//!   `"static"`, `"chimera"`, and `"alloc"`. Because of `spack`'s caching and
//!   RPATH rewriting, the same dynamic library can be shared by every
//!   dependency of this crate.
//! - **`"compiler"` (default):** whether to bring in the entire `libhs`
//!   library, or just `libhs_runtime`, which is unable to [compile patterns]
//!   but can [deserialize them]. This significantly reduces the size of the
//!   code added to the binary.
//! - **`"chimera"`:** whether to link against PCRE and add in extra vectorscan
//!   code to provide the chimera PCRE compatible search library. Conflicts with
//!   `"dynamic"` and requires `"compiler"`.
//!
//! [compile patterns]: crate::database::Database::compile
//! [deserialize them]: crate::database::SerializedDb::deserialize_db
//!
//! Feature flags are also used to gate certain functionality to minimize
//! external dependencies when not in use:
//! - **`"alloc"`:** hook into vectorscan's dynamic memory allocation with
//!   [`crate::alloc`]. Requires `"static"` due to modifying process-global
//!   hooks.
//! - **`"stream"` (default):** supports stream parsing with [`crate::stream`].
//! - **`"vectored"` (default):** supports vectored mode parsing with
//!   [`Mode::VECTORED`].
//! - **`"catch-unwind"` (default):** catches Rust panics in the match callback
//!   before they bubble back up to vectorscan to produce undefined behavior.
//! - **`"async"`:** provides an `async` interface over vectorscan's quirky
//!   callback API using [`tokio`] as described in [Asynchronous String
//!   Scanning].
//! - **`"tokio-impls"`:** implements [`tokio::io::AsyncWrite`] for stream
//!   parsers in [`crate::stream::channel::AsyncStreamWriter`].
//!
//! [Asynchronous String Scanning]: crate::state::Scratch#asynchronous-string-scanning
//! [`Mode::VECTORED`]: crate::flags::Mode::VECTORED

/* Warn for missing docs in general, and hard require crate-level docs. */
#![warn(missing_docs)]
#![deny(rustdoc::missing_crate_level_docs)]
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
