/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use spack::utils::declarative::{bindings, resolve_dependencies};

use cc;
use tokio::task;

#[tokio::main]
async fn main() -> eyre::Result<()> {
  let prefixes = resolve_dependencies().await?;

  task::spawn_blocking(|| {
    cc::Build::new()
      .cpp(true)
      .pic(true)
      .file("src/c-bindings.cpp")
      .include("src")
      .includes(
        prefixes
          .into_iter()
          .map(|p| bindings::get_include_subdir(p)),
      )
      .try_compile("re2_c_bindings")
  })
    .await??;

  Ok(())
}
