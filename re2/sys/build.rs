/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

#![deny(unsafe_code)]
// Turn all warnings into errors!
// #![deny(warnings)]
// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
/* Enable all clippy lints except for many of the pedantic ones. It's a shame this needs to be
 * copied and pasted across crates, but there doesn't appear to be a way to include inner
 * attributes from a common source. */
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

use bindgen;
use spack::{
  self,
  utils::{self, prefix},
  SpackInvocation,
};
use tokio::task;

use std::{io, path::PathBuf};

async fn link_libraries(prefix: prefix::Prefix) -> Result<(), prefix::PrefixTraversalError> {
  let query = prefix::LibsQuery {
    needed_libraries: vec![prefix::LibraryName("re2".to_string())],
    kind: prefix::LibraryType::Static,
  };
  let libs = query.find_libs(&prefix).await?;

  libs.link_libraries();

  Ok(())
}

fn generate_bindings(
  re2_prefix: PathBuf,
  header_path: PathBuf,
  output_path: PathBuf,
) -> Result<(), io::Error> {
  let re2_header_root = re2_prefix.join("include");

  let bindings = bindgen::Builder::default()
    /* FIXME: is there really not a more specific method than "clang_arg()" to add an include
     * search dir??? */
    .clang_arg(format!("-I{}", re2_header_root.display()))
    .header(format!("{}", header_path.display()))
    .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
    .clang_arg("-std=c++17")
    .clang_args(&["-x", "c++"])
    .enable_cxx_namespaces()
    /* FIXME: these only work on ubuntu! */
    .clang_args(&["-cxx-isystem", "/usr/include/c++/12"])
    .clang_args(&["-cxx-isystem", "/usr/include/x86_64-linux-gnu/c++/12"])
    .opaque_type("std::.*")
    .allowlist_item(".*RE2.*");

  let bindings = bindings.generate().unwrap();
  bindings.write_to_file(output_path)?;

  Ok(())
}

#[tokio::main]
async fn main() {
  let spack = SpackInvocation::summon().await.unwrap();

  let re2_prefix = utils::ensure_prefix(spack, "re2".into()).await.unwrap();

  link_libraries(re2_prefix.clone()).await.unwrap();

  let libstdcpp_prefix = prefix::Prefix {
    /* FIXME: this only works on ubuntu! */
    path: PathBuf::from("/usr/lib/gcc/x86_64-linux-gnu/12"),
  };
  let query = prefix::LibsQuery {
    needed_libraries: vec![prefix::LibraryName("stdc++".to_string())],
    kind: prefix::LibraryType::Dynamic,
  };
  let libs = query.find_libs(&libstdcpp_prefix).await.unwrap();
  libs.link_libraries();

  let header_path = PathBuf::from("src/re2.hpp");
  let bindings_path = PathBuf::from("src/bindings.rs");
  task::spawn_blocking(move || generate_bindings(re2_prefix.path, header_path, bindings_path))
    .await
    .unwrap()
    .unwrap();
}
