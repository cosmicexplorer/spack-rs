/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Get a copy of spack.

use crate::{utils, versions::re2_patches::*};

use displaydoc::Display;
use flate2::read::GzDecoder;
use fslock;
use hex::ToHex;
use reqwest;
use sha2::{Digest, Sha256};
use tar;
use thiserror::Error;
use tokio::{
  fs,
  io::{self, AsyncReadExt, AsyncWriteExt},
  task,
};

use std::{
  env,
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
  /// Name intentionally chosen to be overridden later after upstreaming to
  /// spack (?).
  pub async fn get_or_create() -> Result<Self, SummoningError> {
    let path = PathBuf::from(env::var("HOME").expect("$HOME should always be defined!"))
      .join(".spack")
      .join("summonings");
    let p = path.clone();
    task::spawn_blocking(move || utils::safe_create_dir_all_ioerror(&p))
      .await
      .unwrap()?;
    Ok(Self { location: path })
  }

  #[inline]
  pub fn location(&self) -> &Path { &self.location }

  /// We use the hex-encoded checksum value as the ultimate directory name.
  #[inline]
  pub fn dirname(&self) -> String { RE2_PATCHES_SHA256SUM.encode_hex() }

  /// The path to unpack the tar archive into.
  #[inline]
  pub fn unpacking_path(&self) -> PathBuf { self.location.join(RE2_PATCHES_TOPLEVEL_COMPONENT) }

  /// The path to download the release tarball to.
  #[inline]
  pub fn tarball_path(&self) -> PathBuf { self.location.join(format!("{}.tar.gz", self.dirname())) }

  /// The path to the root of the spack repo, through a symlink.
  ///
  /// FIXME: Note that this repeats the
  /// [`RE2_PATCHES_TOPLEVEL_COMPONENT`] component
  /// used in [`Self::unpacking_path`].
  #[inline]
  pub fn repo_root(&self) -> PathBuf { self.unpacking_path().join(RE2_PATCHES_TOPLEVEL_COMPONENT) }

  /// The path to the spack script in the spack repo, through a symlink.
  #[inline]
  pub fn spack_script(&self) -> PathBuf { self.repo_root().join("bin").join("spack") }
}

struct SpackTarball {
  downloaded_location: PathBuf,
}

impl SpackTarball {
  #[inline]
  pub fn downloaded_path(&self) -> &Path { self.downloaded_location.as_ref() }

  async fn check_tarball_digest(
    tgz_path: &Path,
    tgz: &mut fs::File,
  ) -> Result<Self, SummoningError> {
    /* If we have a file already, we just need to check the digest. */
    let mut tarball_bytes: Vec<u8> = vec![];
    tgz.read_to_end(&mut tarball_bytes).await?;
    let mut hasher = Sha256::new();
    hasher.update(&tarball_bytes);
    let checksum: [u8; 32] = hasher.finalize().into();
    if checksum == RE2_PATCHES_SHA256SUM {
      Ok(Self {
        downloaded_location: tgz_path.to_path_buf(),
      })
    } else {
      Err(SummoningError::Checksum(
        format!("file://{}", tgz_path.display()),
        RE2_PATCHES_SHA256SUM.encode_hex(),
        checksum.encode_hex(),
      ))
    }
  }

  /* FIXME: test the checksum checking!!! */
  pub async fn fetch_spack_tarball(cache_dir: CacheDir) -> Result<Self, SummoningError> {
    let tgz_path = cache_dir.tarball_path();

    match fs::File::open(&tgz_path).await {
      Ok(mut tgz) => Self::check_tarball_digest(&tgz_path, &mut tgz).await,
      Err(e) if e.kind() == io::ErrorKind::NotFound => {
        /* If we don't already have a file, we download it! */
        let lockfile_name: PathBuf = format!("{}.tgz.lock", cache_dir.dirname()).into();
        let lockfile_path = cache_dir.location().join(lockfile_name);
        let mut lockfile = task::spawn_blocking(move || fslock::LockFile::open(&lockfile_path))
          .await
          .unwrap()?;
        /* This unlocks the lockfile upon drop! */
        let _lockfile = task::spawn_blocking(move || {
          lockfile.lock_with_pid()?;
          Ok::<_, io::Error>(lockfile)
        })
        .await
        .unwrap()?;
        /* FIXME: delete the lockfile after the proof is written! */

        /* See if the target file was created since we locked the lockfile. */
        if let Ok(mut tgz) = fs::File::open(&tgz_path).await {
          /* If so, check the digest! */
          return Self::check_tarball_digest(&tgz_path, &mut tgz).await;
        }

        eprintln!(
          "downloading spack {} from {}...",
          RE2_PATCHES_TOPLEVEL_COMPONENT, RE2_PATCHES_SPACK_URL,
        );
        let resp = reqwest::get(RE2_PATCHES_SPACK_URL).await?;
        let tarball_bytes = resp.bytes().await?;
        let mut hasher = Sha256::new();
        hasher.update(&tarball_bytes);
        let checksum: [u8; 32] = hasher.finalize().into();
        if checksum == RE2_PATCHES_SHA256SUM {
          let mut tgz = fs::File::create(&tgz_path).await?;
          tgz.write_all(&tarball_bytes).await?;
          tgz.sync_all().await?;
          Ok(Self {
            downloaded_location: tgz_path.to_path_buf(),
          })
        } else {
          Err(SummoningError::Checksum(
            RE2_PATCHES_SPACK_URL.to_string(),
            RE2_PATCHES_SHA256SUM.encode_hex(),
            checksum.encode_hex(),
          ))
        }
      },
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
  cache_dir: CacheDir,
}

impl SpackRepo {
  #[inline]
  pub(crate) fn cache_location(&self) -> &Path { self.cache_dir.location() }

  pub(crate) fn unzip_archive(from: &Path, into: &Path) -> Result<Option<()>, SummoningError> {
    match std::fs::File::open(from) {
      Ok(tgz) => {
        let gz_decoded = GzDecoder::new(tgz);
        let mut archive = tar::Archive::new(gz_decoded);
        Ok(Some(archive.unpack(into)?))
      },
      Err(e) if e.kind() == io::ErrorKind::NotFound => Ok(None),
      Err(e) => Err(e.into()),
    }
  }

  async fn unzip_spack_archive(cache_dir: CacheDir) -> Result<Option<()>, SummoningError> {
    let from = cache_dir.tarball_path();
    let into = cache_dir.unpacking_path();
    task::spawn_blocking(move || Self::unzip_archive(&from, &into))
      .await
      .unwrap()
  }

  pub(crate) async fn get_spack_script(cache_dir: CacheDir) -> Result<Self, SummoningError> {
    let path = cache_dir.spack_script();
    let _ = fs::File::open(&path).await?;
    Ok(Self {
      script_path: path,
      repo_path: cache_dir.repo_root(),
      cache_dir,
    })
  }

  async fn ensure_unpacked(
    current_link_path: PathBuf,
    cache_dir: &CacheDir,
  ) -> Result<(), SummoningError> {
    match fs::read_dir(&current_link_path).await {
      Ok(_) => Ok(()),
      Err(e) if e.kind() == io::ErrorKind::NotFound => {
        /* (2) If the spack repo wasn't found on disk, try finding an adjacent
         * tarball. */

        let lockfile_name: PathBuf = format!("{}.lock", cache_dir.dirname()).into();
        let lockfile_path = cache_dir.location().join(lockfile_name);
        let mut lockfile = task::spawn_blocking(move || fslock::LockFile::open(&lockfile_path))
          .await
          .unwrap()?;
        /* This unlocks the lockfile upon drop! */
        let _lockfile = task::spawn_blocking(move || {
          lockfile.lock_with_pid()?;
          Ok::<_, io::Error>(lockfile)
        })
        .await
        .unwrap()?;

        /* See if the target dir was created since we locked the lockfile. */
        match fs::read_dir(&current_link_path).await {
          /* If so, return early! */
          Ok(_) => Ok::<_, SummoningError>(()),
          /* Otherwise, extract it! */
          Err(e) if e.kind() == io::ErrorKind::NotFound => {
            eprintln!("extracting spack {}...", RE2_PATCHES_TOPLEVEL_COMPONENT,);
            assert!(Self::unzip_spack_archive(cache_dir.clone())
              .await?
              .is_some());
            Ok(())
          },
          Err(e) => Err(e.into()),
        }
      },
      Err(e) => Err(e.into()),
    }
  }

  /// Get the most up-to-date version of spack with appropriate changes.
  ///
  /// If necessary, download the release tarball, validate its checksum, then
  /// expand the tarball. Return the path to the spack root directory.
  pub async fn summon(cache_dir: CacheDir) -> Result<Self, SummoningError> {
    let spack_tarball = SpackTarball::fetch_spack_tarball(cache_dir.clone()).await?;
    dbg!(spack_tarball.downloaded_path());

    let current_link_path = cache_dir.unpacking_path();
    Self::ensure_unpacked(current_link_path, &cache_dir).await?;

    Self::get_spack_script(cache_dir).await
  }
}

/* FIXME: this test will break all the other ones if it modifies the $HOME
 * variable! */
/* #[cfg(test)] */
/* mod test { */
/* use tokio; */

/* #[tokio::test] */
/* async fn test_summon() -> Result<(), super::SummoningError> { */
/* use crate::summoning::*; */
/* use std::fs::File; */

/* let td = tempdir::TempDir::new("spack-summon-test").unwrap(); */
/* std::env::set_var("HOME", td.path()); */
/* let cache_dir = CacheDir::get_or_create()?; */
/* let spack_exe = SpackRepo::summon(cache_dir).await?; */
/* let _ = File::open(&spack_exe.script_path).expect("spack script should
 * exist"); */
/* Ok(()) */
/* } */
/* } */
