/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

/* use super_process::{base, exe, fs, stream, sync}; */

pub mod python {
  use super_process::{
    base::{self, CommandBase},
    exe, fs,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use displaydoc::Display;
  use once_cell::sync::Lazy;
  use regex::Regex;
  use thiserror::Error;

  use std::{env, ffi::OsString, io, path::Path, str};

  /// Things that can go wrong when detecting python.
  #[derive(Debug, Display, Error)]
  pub enum PythonError {
    /// unknown error: {0}
    UnknownError(String),
    /// error executing command: {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// error setting up command: {0}
    Setup(#[from] base::SetupErrorWrapper),
    /// io error: {0}
    Io(#[from] io::Error),
  }

  #[derive(Debug, Clone)]
  pub struct PythonInvocation {
    exe: exe::Exe,
    inner: exe::Command,
  }

  #[async_trait]
  impl CommandBase for PythonInvocation {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self { exe, mut inner } = self;
      inner.unshift_new_exe(exe);
      Ok(inner)
    }
  }

  /// Refers to a particular python executable [`PYTHON_CMD`] first on the
  /// `$PATH`.
  #[derive(Debug, Clone)]
  pub struct FoundPython {
    pub exe: exe::Exe,
    /// Version string parsed from the python executable.
    pub version: String,
  }

  /// Pattern we match against when executing [`Python::detect`].
  pub static PYTHON_VERSION_REGEX: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"^Python (3\.[0-9]+\.[0-9]+).*\n$").unwrap());

  impl FoundPython {
    fn determine_python_exename() -> exe::Exe {
      let exe_name: OsString = env::var_os("SPACK_PYTHON").unwrap_or_else(|| "python3".into());
      let exe_path = Path::new(&exe_name).to_path_buf();
      exe::Exe(fs::File(exe_path))
    }

    /// Check for a valid python installation by parsing the output of
    /// `--version`.
    pub async fn detect() -> Result<Self, PythonError> {
      let py = Self::determine_python_exename();
      let command = PythonInvocation {
        exe: py.clone(),
        inner: exe::Command {
          argv: ["--version"].as_ref().into(),
          ..Default::default()
        },
      }
      .setup_command()
      .await
      .map_err(|e| e.with_context(format!("in FoundPython::detect(py = {:?})", &py)))?;
      let output = command.invoke().await?;
      let stdout = str::from_utf8(&output.stdout).map_err(|e| {
        PythonError::UnknownError(format!(
          "could not parse utf8 from '{} --version' stdout ({}); received:\n{:?}",
          &py, &e, &output.stdout
        ))
      })?;
      match PYTHON_VERSION_REGEX.captures(stdout) {
        Some(m) => Ok(Self {
          exe: py,
          version: m.get(1).unwrap().as_str().to_string(),
        }),
        None => Err(PythonError::UnknownError(format!(
          "could not parse '{} --version'; received:\n(stdout):\n{}",
          py, &stdout,
        ))),
      }
    }

    pub(crate) fn with_python_exe(self, inner: exe::Command) -> PythonInvocation {
      let Self { exe, .. } = self;
      PythonInvocation { exe, inner }
    }
  }

  #[cfg(test)]
  mod test {
    use super::*;

    use tokio;

    #[tokio::test]
    async fn test_detect_python() -> Result<(), crate::Error> {
      let _python = FoundPython::detect().await.unwrap();
      Ok(())
    }
  }
}

pub mod spack {
  use super::python;
  use crate::{commands, summoning};
  use super_process::{
    base::{self, CommandBase},
    exe, fs,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use displaydoc::Display;
  use thiserror::Error;

  use std::{
    io,
    path::{Path, PathBuf},
    str,
  };

  #[derive(Debug, Display, Error)]
  pub enum InvocationSummoningError {
    /// error validating arguments: {0}
    Validation(#[from] base::SetupErrorWrapper),
    /// error executing command: {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// error summoning: {0}
    Summon(#[from] summoning::SummoningError),
    /// error finding compilers: {0}
    CompilerFind(#[from] commands::compiler_find::CompilerFindError),
    /// error bootstrapping: {0}
    Bootstrap(#[from] commands::install::InstallError),
    /// error location python: {0}
    Python(#[from] python::PythonError),
    /// io error: {0}
    Io(#[from] io::Error),
  }

  /// Builder for spack subprocesss.
  #[derive(Debug, Clone)]
  pub struct SpackInvocation {
    /// Information about the python executable used to execute spack with.
    python: python::FoundPython,
    /// Information about the spack checkout.
    repo: summoning::SpackRepo,
    /// Version parsed from executing with '--version'.
    #[allow(dead_code)]
    pub version: String,
  }

  pub(crate) static SUMMON_CUR_PROCESS_LOCK: once_cell::sync::Lazy<tokio::sync::Mutex<()>> =
    once_cell::sync::Lazy::new(|| tokio::sync::Mutex::new(()));

  impl SpackInvocation {
    pub(crate) fn cache_location(&self) -> &Path { self.repo.cache_location() }

    /// Create an instance.
    ///
    /// You should prefer to call [`Self::clone`] on the first instance you
    /// construct instead of repeatedly calling this method when executing
    /// multiple spack subprocesss in a row.
    pub async fn create(
      python: python::FoundPython,
      repo: summoning::SpackRepo,
    ) -> Result<Self, InvocationSummoningError> {
      let script_path = format!("{}", repo.script_path.display());
      let command = python
        .clone()
        .with_python_exe(exe::Command {
          argv: [&script_path, "--version"].as_ref().into(),
          ..Default::default()
        })
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("with py {:?} and repo {:?}", &python, &repo)))?;
      let output = command.clone().invoke().await?;
      let version = str::from_utf8(&output.stdout)
        .map_err(|e| format!("utf8 decoding error {}: from {:?}", e, &output.stdout))
        .and_then(|s| {
          s.strip_suffix('\n')
            .ok_or_else(|| format!("failed to strip final newline from output: '{}'", s))
        })
        .map_err(|e: String| {
          python::PythonError::UnknownError(format!(
            "error parsing '{} {} --version' output: {}",
            &python.exe, &script_path, e
          ))
        })?
        .to_string();
      Ok(Self {
        python,
        repo,
        version,
      })
    }

    async fn ensure_compilers_found(&self) -> Result<(), InvocationSummoningError> {
      let find_site_compilers = commands::compiler_find::CompilerFind {
        spack: self.clone(),
        paths: vec![PathBuf::from("/usr/bin")],
        scope: Some("site".to_string()),
      };
      find_site_compilers.compiler_find().await?;
      Ok(())
    }

    async fn bootstrap(
      &self,
      cache_dir: summoning::CacheDir,
    ) -> Result<(), InvocationSummoningError> {
      let bootstrap_proof_name: PathBuf = format!("{}.bootstrap_proof", cache_dir.dirname()).into();
      let bootstrap_proof_path = cache_dir.location().join(bootstrap_proof_name);

      match tokio::fs::File::open(&bootstrap_proof_path).await {
        Ok(_) => return Ok(()),
        /* If not found, continue. */
        Err(e) if e.kind() == io::ErrorKind::NotFound => (),
        Err(e) => return Err(e.into()),
      }

      let bootstrap_lock_name: PathBuf = format!("{}.bootstrap_lock", cache_dir.dirname()).into();
      let bootstrap_lock_path = cache_dir.location().join(bootstrap_lock_name);
      let mut lockfile =
        tokio::task::spawn_blocking(move || fslock::LockFile::open(&bootstrap_lock_path))
          .await
          .unwrap()?;
      /* This unlocks the lockfile upon drop! */
      let _lockfile = tokio::task::spawn_blocking(move || {
        lockfile.lock_with_pid()?;
        Ok::<_, io::Error>(lockfile)
      })
      .await
      .unwrap()?;

      /* See if the target file was created since we locked the lockfile. */
      if tokio::fs::File::open(&bootstrap_proof_path).await.is_ok() {
        /* If so, return early! */
        return Ok(());
      }

      eprintln!(
        "bootstrapping spack {}",
        crate::versions::patches::PATCHES_TOPLEVEL_COMPONENT,
      );

      self.ensure_compilers_found().await?;

      let bootstrap_install = commands::install::Install {
        spack: self.clone(),
        spec: commands::CLISpec::new("zlib"),
        verbosity: Default::default(),
        env: None,
        repos: None,
      };
      let installed_spec = bootstrap_install.install_find().await?;

      use tokio::io::AsyncWriteExt;
      let mut proof = tokio::fs::File::create(bootstrap_proof_path).await?;
      proof
        .write_all(format!("{}", installed_spec.hashed_spec()).as_bytes())
        .await?;

      Ok(())
    }

    /// Create an instance via [`Self::create`], with good defaults.
    pub async fn summon() -> Result<Self, InvocationSummoningError> {
      /* Our use of file locking within the summoning process does not
       * differentiate between different threads within the same process, so
       * we additionally lock in-process here. */
      let _lock = SUMMON_CUR_PROCESS_LOCK.lock().await;

      let python = python::FoundPython::detect().await?;
      let cache_dir = summoning::CacheDir::get_or_create().await?;
      let spack_repo = summoning::SpackRepo::summon(cache_dir.clone()).await?;
      let spack = Self::create(python, spack_repo).await?;
      spack.bootstrap(cache_dir).await?;
      Ok(spack)
    }

    /// Get a [`CommandBase`] instance to execute spack with the given `argv`.
    pub(crate) fn with_spack_exe(self, inner: exe::Command) -> ReadiedSpackInvocation {
      let Self { python, repo, .. } = self;
      ReadiedSpackInvocation {
        python,
        repo,
        inner,
      }
    }
  }

  #[cfg(test)]
  mod test {
    use super::*;

    use crate::{subprocess::python::*, summoning::*};

    use tokio;

    #[tokio::test]
    async fn test_summon() -> Result<(), crate::Error> {
      let spack = SpackInvocation::summon().await?;
      // This is the current version number for the spack installation.
      assert_eq!(spack.version, "1.0.0.dev0");
      Ok(())
    }

    #[tokio::test]
    async fn test_create_invocation() -> Result<(), crate::Error> {
      let _lock = SUMMON_CUR_PROCESS_LOCK.lock().await;

      // Access a few of the relevant files and directories.
      let python = FoundPython::detect().await.unwrap();
      let cache_dir = CacheDir::get_or_create().await.unwrap();
      let spack_exe = SpackRepo::summon(cache_dir).await.unwrap();
      let spack = SpackInvocation::create(python, spack_exe).await?;

      // This is the current version number for the spack installation.
      assert_eq!(spack.version, "1.0.0.dev0");
      Ok(())
    }
  }

  pub(crate) struct ReadiedSpackInvocation {
    pub python: python::FoundPython,
    pub repo: summoning::SpackRepo,
    pub inner: exe::Command,
  }

  #[async_trait]
  impl base::CommandBase for ReadiedSpackInvocation {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self {
        python,
        repo:
          summoning::SpackRepo {
            script_path,
            repo_path,
            ..
          },
        mut inner,
      } = self;

      assert!(inner.wd.is_none(), "assuming working dir was not yet set");
      inner.wd = Some(fs::Directory(repo_path));

      assert!(inner.exe.is_empty());
      inner.unshift_new_exe(exe::Exe(fs::File(script_path)));
      let py = python.with_python_exe(inner);

      Ok(py.setup_command().await?)
    }
  }
}
