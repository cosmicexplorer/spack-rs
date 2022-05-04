/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Get a copy of spack.

use crate::utils;

use displaydoc::Display;
use flate2::read::GzDecoder;
use hex::ToHex;
use reqwest;
use sha2::{Digest, Sha256};
use tar;
use thiserror::Error;

use std::{
  env, fs,
  io::{self, Read, Write},
  path::{Path, PathBuf},
};

/// Errors that can occur while summoning.
#[derive(Debug, Display, Error)]
pub enum SummoningError {
  /// reqwest error: {0}
  Http(#[from] reqwest::Error),
  /// i/o error: {0}
  Io(#[from] io::Error),
  /// checksum error from URL {0}; expected {1}, got {2}
  Checksum(String, String, String),
  /// unknown error: {0}
  UnknownError(String),
}

/// Base directory for cached spack installs.
#[derive(Clone, Debug)]
pub struct CacheDir {
  location: PathBuf,
}

impl CacheDir {
  /// Goes to `~/.spack/summonings`.
  ///
  /// Name intentionally chosen to be overridden later after upstreaming to spack (?).
  pub fn get_or_create() -> Result<Self, SummoningError> {
    let path = PathBuf::from(env::var("HOME").expect("$HOME should always be defined!"))
      .join(".spack")
      .join("summonings");
    utils::safe_create_dir_all_ioerror(path.as_ref())?;
    Ok(Self { location: path })
  }

  /// We use the hex-encoded checksum value as the ultimate directory name.
  #[inline]
  pub fn dirname(&self) -> String {
    crate::EMCC_URL_SHA256SUM.encode_hex()
  }

  /// The path to unpack the tar archive into.
  #[inline]
  pub fn unpacking_path(&self) -> PathBuf {
    self
      .location
      .join(crate::EMCC_SPACK_ARCHIVE_TOPLEVEL_COMPONENT)
  }

  /// The path to download the release tarball to.
  #[inline]
  pub fn tarball_path(&self) -> PathBuf {
    self.location.join(format!("{}.tar.gz", self.dirname()))
  }

  /// The path to the root of the spack repo, through a symlink.
  ///
  /// FIXME: Note that this repeats the [`crate::EMCC_SPACK_ARCHIVE_TOPLEVEL_COMPONENT`] component
  /// used in [`Self::unpacking_path`].
  #[inline]
  pub fn repo_root(&self) -> PathBuf {
    self
      .unpacking_path()
      .join(crate::EMCC_SPACK_ARCHIVE_TOPLEVEL_COMPONENT)
  }

  /// The path to the spack script in the spack repo, through a symlink.
  #[inline]
  pub fn spack_script(&self) -> PathBuf {
    self.repo_root().join("bin").join("spack")
  }
}

struct SpackTarball {
  downloaded_location: PathBuf,
}

impl SpackTarball {
  pub fn downloaded_path(&self) -> &Path {
    self.downloaded_location.as_ref()
  }

  pub fn unzip(self, cache_dir: CacheDir) -> Result<Option<()>, SummoningError> {
    SpackRepo::unzip_archive(self.downloaded_path(), &cache_dir.unpacking_path())
  }

  /* FIXME: test the checksum checking!!! */
  pub async fn fetch_spack_tarball(cache_dir: CacheDir) -> Result<Self, SummoningError> {
    let tgz_path = cache_dir.tarball_path();

    match fs::File::open(&tgz_path) {
      Ok(mut tgz) => {
        /* If we have a file already, we just need to check the digest. */
        let mut tarball_bytes: Vec<u8> = vec![];
        tgz.read_to_end(&mut tarball_bytes)?;
        let mut hasher = Sha256::new();
        hasher.update(&tarball_bytes);
        let checksum: [u8; 32] = hasher.finalize().into();
        if checksum == crate::EMCC_URL_SHA256SUM {
          Ok(Self {
            downloaded_location: tgz_path,
          })
        } else {
          Err(SummoningError::Checksum(
            format!("file://{}", tgz_path.display()),
            crate::EMCC_URL_SHA256SUM.encode_hex(),
            checksum.encode_hex(),
          ))
        }
      }
      Err(e) if e.kind() == io::ErrorKind::NotFound => {
        /* If we don't already have a file, we download it! */
        let resp = reqwest::get(crate::EMCC_CAPABLE_SPACK_URL).await?;
        let tarball_bytes = resp.bytes().await?;
        let mut hasher = Sha256::new();
        hasher.update(&tarball_bytes);
        let checksum: [u8; 32] = hasher.finalize().into();
        if checksum == crate::EMCC_URL_SHA256SUM {
          let mut tgz = fs::File::create(&tgz_path)?;
          tgz.write_all(&tarball_bytes)?;
          tgz.sync_all()?;
          Ok(Self {
            downloaded_location: tgz_path,
          })
        } else {
          Err(SummoningError::Checksum(
            crate::EMCC_CAPABLE_SPACK_URL.to_string(),
            crate::EMCC_URL_SHA256SUM.encode_hex(),
            checksum.encode_hex(),
          ))
        }
      }
      Err(e) => Err(e.into()),
    }
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
  pub(crate) fn unzip_archive(from: &Path, into: &Path) -> Result<Option<()>, SummoningError> {
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

  fn unzip_spack_archive(cache_dir: CacheDir) -> Result<Option<()>, SummoningError> {
    let from = cache_dir.tarball_path();
    let into = cache_dir.unpacking_path();
    Self::unzip_archive(&from, &into)
  }

  fn get_spack_script(cache_dir: CacheDir) -> Result<Self, SummoningError> {
    let path = cache_dir.spack_script();
    let _ = fs::File::open(&path)?;
    Ok(Self {
      script_path: path,
      repo_path: cache_dir.repo_root(),
    })
  }

  /// Get the most up-to-date version of spack with appropriate changes.
  ///
  /// If necessary, download the release tarball, validate its checksum, then expand the
  /// tarball. Return the path to the spack root directory.
  ///```
  /// use spack::summoning::*;
  /// use std::fs::File;
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// # let td = tempdir::TempDir::new("spack-summon-test").unwrap();
  /// # std::env::set_var("HOME", td.path());
  /// let cache_dir = CacheDir::get_or_create().unwrap();
  /// let spack_exe = SpackRepo::summon(cache_dir).await.unwrap();
  /// let _ = File::open(&spack_exe.script_path).expect("spack script should exist");
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub async fn summon(cache_dir: CacheDir) -> Result<Self, SummoningError> {
    let current_link_path = cache_dir.unpacking_path();

    let () = match fs::read_dir(current_link_path) {
      Ok(_) => Ok(()),
      Err(e) if e.kind() == io::ErrorKind::NotFound => {
        /* (2) If the spack repo wasn't found on disk, try finding an adjacent tarball. */
        match Self::unzip_spack_archive(cache_dir.clone())? {
          /* (2.1) The untarring worked! */
          Some(()) => Ok(()),
          /* (3) If the tarball wasn't there either, try fetching it from the internet. */
          None => {
            let spack_tarball = SpackTarball::fetch_spack_tarball(cache_dir.clone()).await?;
            /* (3.1) After fetching it, we need to try extracting it again. */
            spack_tarball.unzip(cache_dir.clone())?.ok_or_else(|| {
              SummoningError::UnknownError(format!("unzipping archive at {:?} failed!", &cache_dir))
            })
          }
        }
      }
      Err(e) => Err(e.into()),
    }?;

    Ok(Self::get_spack_script(cache_dir)?)
  }
}
