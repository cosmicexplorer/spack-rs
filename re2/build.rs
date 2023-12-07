/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use std::env;

fn main() {
  /* We need to propagate the rpath from the spack-compiled re2 shared lib into
   * every crate that executes an re2 method directly. This is not an issue
   * when building re2 statically. Cargo provides a somewhat-hidden "links"
   * attribute which enables bubbling up build output from dependencies to
   * dependee build scripts: https://doc.rust-lang.org/cargo/reference/build-script-examples.html#using-another-sys-crate. */
  if cfg!(feature = "dynamic") {
    if let Ok(joined_rpath) = env::var("DEP_RE2_JOINED_RPATH") {
      for dir in joined_rpath.split(":").filter(|s| !s.is_empty()) {
        println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir);
      }
    } else {
      unreachable!("re2-sys dep should have populated cargo:joined_rpath!");
    }
  }
}
