/* Copyright 2023-2024 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#![allow(clippy::single_component_path_imports)]

use spack::utils::declarative::resolve;

use bindgen;
use cc;
use tokio::{fs, task};

use std::{env, path::PathBuf};

#[tokio::main]
async fn main() -> eyre::Result<()> {
  /* let outfile = PathBuf::from("src").join("bindings.rs"); */
  let outfile = PathBuf::from(env::var("OUT_DIR").unwrap()).join("bindings.rs");

  if env::var("DOCS_RS").is_ok() {
    let stub = fs::read("src/re2_stub.rs").await?;
    fs::write(outfile, stub).await?;
    println!("cargo:joined_rpath=");
    return Ok(());
  }

  if cfg!(feature = "static") {
    assert!(
      !cfg!(feature = "dynamic"),
      "dynamic and static cannot coexist"
    );
  } else {
    assert!(
      cfg!(feature = "dynamic"),
      "either dynamic or static must be chosen"
    );
  }

  let prefixes = resolve::resolve_dependencies().await?;

  println!("cargo:rerun-if-changed=src/c-bindings.cpp");
  let mut bindings = bindgen::Builder::default()
    .clang_args(&["-x", "c++"])
    .clang_arg("-std=c++20")
    .enable_cxx_namespaces()
    .opaque_type("std::.*")
    .generate_comments(true)
    .fit_macro_constants(true)
    .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
    .header("src/c-bindings.hpp");
  bindings = bindings.allowlist_item("re2::.*");
  bindings = bindings.allowlist_item("re2_c_bindings::.*");
  for p in prefixes.iter() {
    bindings = bindings.clang_arg(format!("-I{}", p.include_subdir().display()));
  }
  bindings.generate()?.write_to_file(&outfile)?;

  task::spawn_blocking(|| {
    cc::Build::new()
      .cpp(true)
      .pic(true)
      .std("c++20")
      .file("src/c-bindings.cpp")
      .include("src")
      .includes(prefixes.into_iter().map(|p| p.include_subdir()))
      .try_compile("re2_c_bindings")
  })
  .await??;

  println!("cargo:rustc-link-lib=stdc++");

  Ok(())
}
