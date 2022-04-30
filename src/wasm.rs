/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Utilities for building code with [wasm] support via [emscripten].
//!
//! [wasm]: https://webassembly.org
//! [emscripten]: https://emscripten.org

use crate::commands::find;

const LLVM_FOR_WASM: &str = "llvm@14:\
+lld+clang+multiple-definitions\
~compiler-rt~tools-extra-clang~libcxx~gold~openmp~internal_unwind~polly \
targets=webassembly";

/// Ensure that a version of llvm is installed that is able to support emscripten.
///```
/// # fn main() -> Result<(), spack::Error> {
/// # tokio_test::block_on(async {
/// use spack::command::{Command, sync::SyncInvocable};
///
/// // Locate all the executables.
/// let spack = spack::Invocation::summon().await?;
///
/// // Let's look for an `llvm` installation, and find the `llvm-config` executable.
/// let llvm = spack::wasm::ensure_wasm_ready_llvm(spack.clone()).await?;
/// let llvm_prefix = spack::ensure_prefix(spack, llvm.hashed_spec()).await?;
/// let llvm_config_path = llvm_prefix.join("bin").join("llvm-config");
///
/// // Let's make sure the executable can be executed successfully!
/// let command = Command {
///   exe: llvm_config_path,
///   argv: ["--targets-built"].as_ref().into(),
///   ..Default::default()
/// };
/// let output = command.invoke().await.expect("expected llvm-config command to succeed");
/// let stdout = std::str::from_utf8(&output.stdout).unwrap();
/// assert!(stdout.contains("WebAssembly"));
/// # Ok(())
/// # }) // async
/// # }
///```
pub async fn ensure_wasm_ready_llvm(
  spack: crate::Invocation,
) -> Result<find::FoundSpec, crate::Error> {
  let llvm_found_spec = crate::ensure_installed(spack, LLVM_FOR_WASM.into()).await?;
  Ok(llvm_found_spec)
}
