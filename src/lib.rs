/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Rust wrappers for [spack](https://github.com/spack/spack). For use in [build scripts](https://doc.rust-lang.org/cargo/reference/build-scripts.html).

#![deny(unsafe_code)]
/* Turn all warnings into errors! */
/* #![deny(warnings)] */
/* Warn for missing docs in general, and hard require crate-level docs. */
#![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
/* Enable all clippy lints except for many of the pedantic ones. It's a shame this needs to be
 * copied and pasted across crates, but there doesn't appear to be a way to include inner attributes
 * from a common source. */
#![deny(
  clippy::all,
  clippy::default_trait_access,
  clippy::expl_impl_clone_on_copy,
  clippy::if_not_else,
  clippy::needless_continue,
  clippy::unseparated_literal_suffix,
  clippy::used_underscore_binding
)]
/* We use inner modules in several places in this crate for ergonomics. */
#![allow(clippy::module_inception)]
/* It is often more clear to show that nothing is being moved. */
#![allow(clippy::match_ref_pats)]
/* Subjective style. */
#![allow(
  clippy::len_without_is_empty,
  clippy::redundant_field_names,
  clippy::too_many_arguments,
  clippy::single_component_path_imports
)]
/* Default isn't as big a deal as people seem to think it is. */
#![allow(clippy::new_without_default, clippy::new_ret_no_self)]
/* Arc<Mutex> can be more clear than needing to grok Orderings: */
#![allow(clippy::mutex_atomic)]

use displaydoc::Display;
use flate2::read::GzDecoder;
use hex::ToHex;
use hex_literal::hex;
use reqwest;
use sha2::{Digest, Sha256};
use tar;
use thiserror::Error;

use std::{
  env, fs,
  io::{self, Write},
  path::{Path, PathBuf},
};

/// Errors that can occur.
#[derive(Debug, Display, Error)]
pub enum Error {
  /// reqwest error: {0}
  Http(#[from] reqwest::Error),
  /// io error: {0}
  Io(#[from] io::Error),
  /// checksum error from URL {0}; expected {1}, got {2}
  Checksum(&'static str, String, String),
  /// unknown error: {0}
  UnknownError(String),
}

/// Goes to `~/.spack/summonings`.
///
/// Name intentionally chosen to be overridden later after upstreaming to spack (?).
fn get_or_create_cache_dir() -> Result<PathBuf, Error> {
  let path = PathBuf::from(env::var("HOME").expect("$HOME should always be defined!"))
    .join(".spack")
    .join("summonings");
  safe_create_dir_all_ioerror(path.as_ref())?;
  Ok(path)
}

const EMCC_CAPABLE_SPACK_URL: &str =
  "https://github.com/cosmicexplorer/spack/archive/refs/tags/v0.17.2.0-emcc.tar.gz";
const EMCC_URL_SHA256SUM: [u8; 32] =
  hex!("64309696f958e98dcaf80f843589084559d6dda6d54f06556279a1a7be4500cf");

async fn fetch_spack_tarball(into: &Path) -> Result<(), Error> {
  let resp = reqwest::get(EMCC_CAPABLE_SPACK_URL).await?;
  let tarball_bytes = resp.bytes().await?;
  let mut hasher = Sha256::new();
  hasher.update(&tarball_bytes);
  let checksum: [u8; 32] = hasher.finalize().into();
  if checksum == EMCC_URL_SHA256SUM {
    let mut tgz = fs::File::create(into)?;
    tgz.write_all(&tarball_bytes)?;
    tgz.sync_all()?;
    Ok(())
  } else {
    Err(Error::Checksum(
      EMCC_CAPABLE_SPACK_URL,
      EMCC_URL_SHA256SUM.encode_hex(),
      checksum.encode_hex(),
    ))
  }
}

fn try_unzip_spack(from: &Path, into: &Path) -> Result<Option<()>, Error> {
  match fs::File::open(from) {
    Ok(tgz) => {
      let gz_decoded = GzDecoder::new(tgz);
      let mut archive = tar::Archive::new(gz_decoded);
      Ok(Some(archive.unpack(into)?))
    }
    Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
    Err(e) => Err(e.into()),
  }
}

/// Get the most up-to-date version of spack with appropriate changes.
///
/// If necessary, download the release tarball, validate its checksum, then expand the
/// tarball. Return the path to the spack root directory.
///
///
///```
/// use std::{fs, env};
/// # fn main() -> Result<(), spack::Error> {
/// # let td = tempdir::TempDir::new("spack-summon-test")?;
/// # env::set_var("HOME", td.path());
/// let spack_dir = tokio_test::block_on(async { spack::summon_spack().await })?;
/// let _ = fs::read_dir(&spack_dir).expect("spack summon directory should exist");
/// # Ok(())
/// # }
///```
pub async fn summon_spack() -> Result<PathBuf, Error> {
  let cache_path = get_or_create_cache_dir()?;
  let dirname: String = EMCC_URL_SHA256SUM.encode_hex();
  let current_spack_summon = cache_path.join(&dirname);
  match fs::read_dir(&current_spack_summon) {
    Ok(_) => Ok(current_spack_summon),
    Err(e) if e.kind() == io::ErrorKind::NotFound => {
      let archive_name = PathBuf::from(format!("{}.tar.gz", &dirname));
      let tgz_path = cache_path.join(&archive_name);
      match try_unzip_spack(&tgz_path, &current_spack_summon)? {
        Some(()) => Ok(current_spack_summon),
        None => {
          fetch_spack_tarball(&tgz_path).await?;
          match try_unzip_spack(&tgz_path, &current_spack_summon)? {
            Some(()) => Ok(current_spack_summon),
            None => Err(Error::UnknownError(format!(
              "we just downloaded the spack tarball from {} into {}, but we couldn't unzip it to {}?!",
              EMCC_CAPABLE_SPACK_URL,
              tgz_path.display(),
              current_spack_summon.display(),
            ))),
          }
        }
      }
    }
    Err(e) => Err(e.into()),
  }
}

///
/// Like [std::fs::create_dir_all], except handles concurrent calls among multiple
/// threads or processes. Originally lifted from rustc, then from pants.
///
fn safe_create_dir_all_ioerror(path: &Path) -> Result<(), io::Error> {
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
