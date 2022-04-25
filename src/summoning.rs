/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Get a copy of spack.

use crate::{utils, Error};

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
  let resp = reqwest::get(crate::EMCC_CAPABLE_SPACK_URL).await?;
  let tarball_bytes = resp.bytes().await?;
  let mut hasher = Sha256::new();
  hasher.update(&tarball_bytes);
  let checksum: [u8; 32] = hasher.finalize().into();
  if checksum == crate::EMCC_URL_SHA256SUM {
    let mut tgz = fs::File::create(into)?;
    tgz.write_all(&tarball_bytes)?;
    tgz.sync_all()?;
    Ok(())
  } else {
    Err(Error::Checksum(
      crate::EMCC_CAPABLE_SPACK_URL,
      crate::EMCC_URL_SHA256SUM.encode_hex(),
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

/// Location of a spack executable script.
#[derive(Debug, Clone)]
pub struct SpackRepo {
  /// NB: This script was not checked to be executable!
  pub script_path: PathBuf,
  /// This directory *must* exist when returned by [Self::summon].
  pub repo_path: PathBuf,
}

impl SpackRepo {
  /// Get the most up-to-date version of spack with appropriate changes.
  ///
  /// If necessary, download the release tarball, validate its checksum, then expand the
  /// tarball. Return the path to the spack root directory.
  ///
  ///
  ///```
  /// use spack::summoning::SpackRepo;
  /// use std::fs::File;
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// # let td = tempdir::TempDir::new("spack-summon-test")?;
  /// # std::env::set_var("HOME", td.path());
  /// let spack_exe = SpackRepo::summon().await?;
  /// let _ = File::open(&spack_exe.script_path)?;
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub async fn summon() -> Result<Self, Error> {
    let cache_path = get_or_create_cache_dir()?;
    let dirname: String = crate::EMCC_URL_SHA256SUM.encode_hex();
    let repo_base_path = cache_path.join(&dirname);
    let repo_path = repo_base_path.join(crate::EMCC_SPACK_ARCHIVE_TOPLEVEL_COMPONENT);
    let script_path = repo_path.join("bin").join("spack");
    match fs::File::open(&script_path) {
      Ok(_) => Ok(SpackRepo {
        script_path,
        repo_path,
      }),
      Err(e) if e.kind() == io::ErrorKind::NotFound => {
        let archive_name = PathBuf::from(format!("{}.tar.gz", &dirname));
        let tgz_path = cache_path.join(&archive_name);
        match try_unzip_spack(&tgz_path, &repo_base_path)? {
          Some(()) => Ok(SpackRepo {
            script_path,
            repo_path,
          }),
          None => {
            fetch_spack_tarball(&tgz_path).await?;
            match try_unzip_spack(&tgz_path, &repo_base_path)? {
              Some(()) => Ok(SpackRepo { script_path, repo_path }),
              None => Err(Error::UnknownError(format!(
                "we just downloaded the spack tarball from {} into {}, but we couldn't unzip it to {}?!",
                crate::EMCC_CAPABLE_SPACK_URL,
                tgz_path.display(),
                script_path.display(),
            ))),
          }
          }
        }
      }
      Err(e) => Err(e.into()),
    }
  }
}
