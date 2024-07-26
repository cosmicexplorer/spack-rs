/* Copyright 2023-2024 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#![allow(clippy::single_component_path_imports)]

use spack::utils::declarative::resolve;

use bindgen;
use tokio::fs;

use std::{env, path::PathBuf};

#[tokio::main]
async fn main() -> eyre::Result<()> {
  /* let outfile = PathBuf::from("src").join("bindings.rs"); */
  let outfile = PathBuf::from(env::var("OUT_DIR").unwrap()).join("bindings.rs");

  if env::var("DOCS_RS").is_ok() {
    let stub = fs::read("src/pexl_stub.rs").await?;
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

  let mut bindings = bindgen::Builder::default()
    .clang_args(&["-x", "c"])
    .clang_arg("-std=c99")
    .generate_comments(true)
    .fit_macro_constants(true)
    .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
    .header("src/pexl.h");
  bindings = bindings.allowlist_item("pexl_.*");
  bindings = bindings.allowlist_item("PEXL_.*");
  for p in prefixes.iter() {
    bindings = bindings.clang_arg(format!("-I{}", p.include_subdir().display()));
  }
  bindings.generate()?.write_to_file(&outfile)?;

  Ok(())
}
