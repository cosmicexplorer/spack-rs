/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use spack::utils::declarative::{bindings, resolve};

use bindgen;
use tokio::fs;

use std::{env, path::PathBuf};

#[tokio::main]
async fn main() -> eyre::Result<()> {
  /* let outfile = PathBuf::from("src").join("bindings.rs"); */
  let outfile = PathBuf::from(env::var("OUT_DIR").unwrap()).join("bindings.rs");

  if env::var("DOCS_RS").is_ok() {
    let stub = fs::read("src/hs_stub.rs").await?;
    fs::write(outfile, stub).await?;
    println!("cargo:joined_rpath=");
    return Ok(());
  }

  if cfg!(feature = "chimera") {
    assert!(cfg!(feature = "static"), "chimera requires static");
    assert!(cfg!(feature = "compile"), "chimera requires compile");
  } else if cfg!(feature = "dynamic") {
    assert!(
      !cfg!(feature = "static"),
      "dynamic and static are incompatible"
    );
  } else {
    assert!(
      cfg!(feature = "static"),
      "either static or dynamic is required"
    );
  }

  let prefixes = resolve::resolve_dependencies().await?;

  let mut bindings = bindgen::Builder::default()
    .clang_args(&["-x", "c++"])
    .clang_arg("-std=c++20")
    .enable_cxx_namespaces()
    .opaque_type("std::.*")
    /* TODO: generated doc comments for one of the exported functions get parsed as doctests which
     * don't compile. */
    .generate_comments(false)
    .fit_macro_constants(true)
    .header("src/hs.h")
    .raw_line("#[allow(unused, non_camel_case_types, improper_ctypes, clippy::all)]");
  bindings = bindings.allowlist_item("hs.*");
  bindings = bindings.allowlist_item("HS.*");
  bindings = bindings.allowlist_item("ch.*");
  bindings = bindings.allowlist_item("CH.*");
  for p in prefixes.into_iter() {
    bindings = bindings.clang_arg(format!("-I{}", bindings::get_include_subdir(p).display()));
  }
  if cfg!(feature = "chimera") {
    bindings = bindings.clang_arg("-D__INCLUDE_CHIMERA__");
  }
  bindings.generate()?.write_to_file(outfile)?;

  println!("cargo:rustc-link-lib=stdc++");

  Ok(())
}
