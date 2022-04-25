/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Get a copy of spack.

use crate::{utils, Error, EMCC_CAPABLE_SPACK_URL, EMCC_URL_SHA256SUM};

use flate2::read::GzDecoder;
use hex::ToHex;
use reqwest;
use sha2::{Digest, Sha256};
use tar;

use std::{
  env, fs,
  io::{self, Write},
  path::{Path, PathBuf},
};

/// Goes to `~/.spack/summonings`.
///
/// Name intentionally chosen to be overridden later after upstreaming to spack (?).
fn get_or_create_cache_dir() -> Result<PathBuf, Error> {
  let path = PathBuf::from(env::var("HOME").expect("$HOME should always be defined!"))
    .join(".spack")
    .join("summonings");
  utils::safe_create_dir_all_ioerror(path.as_ref())?;
  Ok(path)
}

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
/// # fn main() -> Result<(), spack::Error> {
/// # let td = tempdir::TempDir::new("spack-summon-test")?;
/// # std::env::set_var("HOME", td.path());
/// let spack_dir = tokio_test::block_on(async { spack::summoning::summon_spack().await })?;
/// let _ = std::fs::read_dir(&spack_dir).expect("spack summon directory should exist");
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
