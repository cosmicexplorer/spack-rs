/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use std::env;

fn main() {
  /* We need to propagate the rpath from the spack-compiled vectorscan shared
   * lib into every crate that executes a vectorscan method directly. This is
   * not an issue when building vectorscan statically. Cargo provides a
   * somewhat-hidden "links" attribute which enables bubbling up build output
   * from dependencies to dependee build scripts: https://doc.rust-lang.org/cargo/reference/build-script-examples.html#using-another-sys-crate. */
  if cfg!(feature = "dynamic") {
    if let Ok(joined_rpath) = env::var("DEP_VECTORSCAN_JOINED_RPATH") {
      for dir in joined_rpath.split(':').filter(|s| !s.is_empty()) {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir);
      }
    } else {
      unreachable!("vectorscan-sys dep should have populated cargo:joined_rpath!");
    }
  }
  if cfg!(feature = "alloc") {
    assert!(cfg!(feature = "static"), "alloc requires static");
  }
}
