/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use spack::utils::declarative::{bindings, resolve_dependencies};

use bindgen;

#[tokio::main]
async fn main() -> eyre::Result<()> {
  let prefixes = resolve_dependencies().await?;

  let mut bindings = bindgen::Builder::default()
    .clang_args(&["-x", "c++"])
    .clang_arg("-std=c++20")
    .enable_cxx_namespaces()
    .opaque_type("std::.*")
    /* TODO: generated doc comments for one of the exported functions get parsed as doctests which
     * don't compile. */
    .generate_comments(false)
    .fit_macro_constants(true)
    .header("src/hs.h");
  bindings = bindings.allowlist_item("hs.*");
  bindings = bindings.allowlist_item("HS.*");
  for p in prefixes.iter().cloned() {
    bindings = bindings.clang_arg(format!("-I{}", bindings::get_include_subdir(p).display()));
  }
  bindings.generate()?.write_to_file("src/bindings.rs")?;

  println!("cargo:rustc-link-lib=stdc++");

  Ok(())
}
