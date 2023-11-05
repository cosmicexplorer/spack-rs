/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

use spack::utils::declarative::resolve_dependencies;

#[tokio::main]
async fn main() -> eyre::Result<()> {
  resolve_dependencies().await?;

  Ok(())
}
