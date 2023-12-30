/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Rust wrappers for [`spack`]. For use in [build scripts].
//!
//! [`spack`]: https://github.com/spack/spack
//! [build scripts]: https://doc.rust-lang.org/cargo/reference/build-scripts.html

#![deny(unsafe_code)]
// Turn all warnings into errors!
// #![deny(warnings)]
// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

pub mod commands;
mod lock;
pub mod metadata_spec;
pub mod subprocess;
pub mod summoning;
pub mod utils;

pub use subprocess::spack::SpackInvocation;

use displaydoc::Display;
use thiserror::Error;

/// Constants defining available versions of spack.
///
/// Currently, this crate avoids maintaining a git repository (the typical way
/// spack is distributed) in favor of a checksummed directory corresponding to a
/// precise spack release. The main reason for this is to enable experimental
/// support for wasm compilation via emscripten (see the
/// [`wasm`](crate::utils::wasm) module). Until upstream support for emscripten
/// is merged, the cached build output in `opt/` may refer to packages which are
/// unavailable in spack proper, causing an exception when spack is invoked.
///
/// Figuring out a nicer way to select a compatible spack version (which also
/// works across the entire cargo build graph, which may invoke this crate
/// multiple times) is on the horizon, but until then hardcoding this
/// information is slightly easier to work with.
pub mod versions {
  use hex_literal::hex;

  pub mod patches {
    use super::hex;

    pub const PATCHES_SPACK_URL: &str =
      "https://github.com/cosmicexplorer/spack/archive/refs/tags/cargo-patches-v1.tar.gz";
    pub const PATCHES_SHA256SUM: [u8; 32] =
      hex!("bc921f6caeed7a62df674f9127fd03f0a9c04cd8837f0fe42837efdb6e67833a");
    pub const PATCHES_TOPLEVEL_COMPONENT: &str = "spack-cargo-patches-v1";
  }

  /// The most recently released version of spack.
  pub mod develop {
    use super::hex;

    pub const MOST_RECENT_HARDCODED_SPACK_URL: &str =
      "https://github.com/spack/spack/archive/refs/tags/v0.20.3.tar.gz";
    pub const MOST_RECENT_HARDCODED_URL_SHA256SUM: [u8; 32] =
      hex!("c7deaa2f51502ff6f84f79845d8bd23202b0524f7669d3f779bd2049bc43e177");
    pub const MOST_RECENT_HARDCODED_SPACK_ARCHIVE_TOPLEVEL_COMPONENT: &str = "spack-0.20.3";
  }

  /// A spack branch with support for emscripten as a compiler, enabling
  /// compilation to wasm.
  pub mod emcc {
    use super::hex;

    pub const EMCC_CAPABLE_SPACK_URL: &str =
      "https://github.com/cosmicexplorer/spack/archive/refs/tags/v0.20.0.dev0-emcc.tar.gz";
    pub const EMCC_URL_SHA256SUM: [u8; 32] =
      hex!("fc45a31f0f98f9a781eae8a58e38c13980addd20302c0a7f32dc084e55ba7f2f");
    pub const EMCC_SPACK_ARCHIVE_TOPLEVEL_COMPONENT: &str = "spack-0.20.0.dev0-emcc";
  }
}

/// Errors that can occur.
#[derive(Debug, Display, Error)]
#[ignore_extra_doc_attributes]
pub enum Error {
  /// spack summoning error: {0}
  ///
  /// This will occur if spack itself cannot be set up.
  Summoning(#[from] subprocess::spack::InvocationSummoningError),
  /// spack command failed: {0}
  SpackCommand(#[from] commands::CommandError),
}
