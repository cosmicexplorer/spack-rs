/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

use crate::{
  commands::{self, find, install},
  invocation::{command, spack},
};

use std::{
  fs, io,
  path::{Path, PathBuf},
};

/// Like [`fs::create_dir_all`], except handles concurrent calls among multiple
/// threads or processes. Originally lifted from rustc, then from pants.
pub fn safe_create_dir_all_ioerror(path: &Path) -> Result<(), io::Error> {
  match fs::create_dir(path) {
    Ok(()) => return Ok(()),
    Err(ref e) if e.kind() == io::ErrorKind::AlreadyExists => return Ok(()),
    Err(ref e) if e.kind() == io::ErrorKind::NotFound => {}
    Err(e) => return Err(e),
  }
  match path.parent() {
    Some(p) => safe_create_dir_all_ioerror(p)?,
    None => return Ok(()),
  }
  match fs::create_dir(path) {
    Ok(()) => Ok(()),
    Err(ref e) if e.kind() == io::ErrorKind::AlreadyExists => Ok(()),
    Err(e) => Err(e),
  }
}

/// Install a `spec`, then return its installation root prefix from within `opt/spack/...`.
///
/// The installation via `spack install` will be cached using spack's normal caching mechanisms.
///```
/// # fn main() -> Result<(), spack::Error> {
/// # tokio_test::block_on(async {
/// use spack::command::{Command, sync::SyncInvocable};
///
/// // Locate all the executables.
/// let spack = spack::Invocation::summon().await?;
///
/// // Let's look for an `m4` installation, and find the `m4` executable.
/// let m4_prefix = spack::ensure_prefix(spack, "m4".into()).await?;
/// let m4_bin_path = m4_prefix.join("bin").join("m4");
///
/// // Let's make sure the executable can be executed successfully!
/// let command = Command {
///   exe: m4_bin_path,
///   argv: ["--version"].as_ref().into(),
///   ..Default::default()
/// };
/// let output = command.invoke().await?;
/// assert!(output.stdout.starts_with(b"m4 "));
/// # Ok(())
/// # }) // async
/// # }
///```
pub async fn ensure_prefix(
  spack: spack::Invocation,
  spec: commands::CLISpec,
) -> Result<PathBuf, crate::Error> {
  let install = install::Install {
    spack: spack.clone(),
    spec,
  };
  let found_spec = install
    .clone()
    .install_find()
    .await
    .map_err(|e| commands::CommandError::Install(install, e))?;
  let find_prefix = find::FindPrefix {
    spack,
    spec: found_spec.hashed_spec(),
  };
  let prefix = find_prefix
    .clone()
    .find_prefix()
    .await
    .map_err(|e| commands::CommandError::FindPrefix(find_prefix, e))?
    .expect("when using a spec with a hash, FindPrefix should never return None");
  Ok(prefix)
}
