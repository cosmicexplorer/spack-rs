/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#![allow(clippy::single_component_path_imports)]

//! ???

use spack::utils::declarative::{bindings, resolve_dependencies};

use bindgen;
use cc;
use tokio::task;

#[tokio::main]
async fn main() -> eyre::Result<()> {
  let prefixes = resolve_dependencies().await?;

  let mut bindings = bindgen::Builder::default()
    .clang_args(&["-x", "c++"])
    .clang_arg("-std=c++20")
    .enable_cxx_namespaces()
    .opaque_type("std::.*")
    .generate_comments(true)
    .fit_macro_constants(true)
    .header("src/c-bindings.hpp");
  bindings = bindings.allowlist_item("re2::.*");
  bindings = bindings.allowlist_item("re2_c_bindings::.*");
  for p in prefixes.iter().cloned() {
    bindings = bindings.clang_arg(format!("-I{}", bindings::get_include_subdir(p).display()));
  }
  bindings.generate()?.write_to_file("src/bindings.rs")?;

  println!("cargo:rerun-if-changed=src/c-bindings.cpp");
  task::spawn_blocking(|| {
    cc::Build::new()
      .cpp(true)
      .pic(true)
      .std("c++20")
      .file("src/c-bindings.cpp")
      .include("src")
      .includes(prefixes.into_iter().map(bindings::get_include_subdir))
      .try_compile("re2_c_bindings")
  })
  .await??;

  println!("cargo:rustc-link-lib=stdc++");

  Ok(())
}
