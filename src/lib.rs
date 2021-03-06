/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Rust wrappers for [`spack`]. For use in [build scripts].
//!
//! [`spack`]: https://github.com/spack/spack
//! [build scripts]: https://doc.rust-lang.org/cargo/reference/build-scripts.html

#![deny(unsafe_code)]
/* Turn all warnings into errors! */
/* #![deny(warnings)] */
/* Warn for missing docs in general, and hard require crate-level docs. */
/* #![warn(missing_docs)] */
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
/* Enable all clippy lints except for many of the pedantic ones. It's a shame this needs to be
 * copied and pasted across crates, but there doesn't appear to be a way to include inner attributes
 * from a common source. */
#![deny(
  clippy::all,
  clippy::default_trait_access,
  clippy::expl_impl_clone_on_copy,
  clippy::if_not_else,
  clippy::needless_continue,
  clippy::unseparated_literal_suffix,
  clippy::used_underscore_binding
)]
/* We use inner modules in several places in this crate for ergonomics. */
#![allow(clippy::module_inception)]
/* It is often more clear to show that nothing is being moved. */
#![allow(clippy::match_ref_pats)]
/* Subjective style. */
#![allow(
  clippy::len_without_is_empty,
  clippy::redundant_field_names,
  clippy::too_many_arguments,
  clippy::single_component_path_imports
)]
/* Default isn't as big a deal as people seem to think it is. */
#![allow(clippy::new_without_default, clippy::new_ret_no_self)]
/* Arc<Mutex> can be more clear than needing to grok Orderings: */
#![allow(clippy::mutex_atomic)]

pub mod commands;
pub mod subprocess;
pub mod summoning;
pub mod utils;

pub use subprocess::spack::SpackInvocation;

use displaydoc::Display;
use hex_literal::hex;
use thiserror::Error;

const EMCC_CAPABLE_SPACK_URL: &str =
  "https://github.com/cosmicexplorer/spack/archive/refs/tags/v0.17.2.2-emcc.tar.gz";
const EMCC_URL_SHA256SUM: [u8; 32] =
  hex!("44198c3f82ae3427c64c03e2fb51d2877cd3860b73e5da2cd073aaba1480eb70");
const EMCC_SPACK_ARCHIVE_TOPLEVEL_COMPONENT: &str = "spack-0.17.2.2-emcc";

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
