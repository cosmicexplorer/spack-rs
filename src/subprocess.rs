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
  use lazy_static::lazy_static;
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

  /// Refers to a particular python executable [`PYTHON_CMD`] first on the `$PATH`.
  #[derive(Debug, Clone)]
  pub struct FoundPython {
    pub exe: exe::Exe,
    /// Version string parsed from the python executable.
    pub version: String,
  }

  lazy_static! {
    /// Pattern we match against when executing [`Python::detect`].
    static ref PYTHON_VERSION_REGEX: Regex =
      Regex::new(r"^Python (3\.[0-9]+\.[0-9]+).*\n$").unwrap();
  }

  impl FoundPython {
    fn determine_python_exename() -> exe::Exe {
      let exe_name: OsString = env::var_os("SPACK_PYTHON").unwrap_or_else(|| "python3".into());
      let exe_path = Path::new(&exe_name).to_path_buf();
      exe::Exe(fs::File(exe_path))
    }

    /// Check for a valid python installation by parsing the output of `--version`.
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
      match PYTHON_VERSION_REGEX.captures(&stdout) {
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
      #[allow(unused_variables)]
      let python = FoundPython::detect().await.unwrap();
      Ok(())
    }
  }
}

pub mod spack {
  use super::python;
  use crate::summoning;
  use super_process::{
    base::{self, CommandBase},
    exe, fs,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use displaydoc::Display;
  use thiserror::Error;

  use std::{io, str};

  #[derive(Debug, Display, Error)]
  pub enum InvocationSummoningError {
    /// error validating arguments: {0}
    Validation(#[from] base::SetupErrorWrapper),
    /// error executing command: {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// error summoning: {0}
    Summon(#[from] summoning::SummoningError),
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

  impl SpackInvocation {
    /// Create an instance.
    ///
    /// You should prefer to call [`Self::clone`] on the first instance you construct instead of
    /// repeatedly calling this method when executing multiple spack subprocesss in a row.
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
          s.strip_suffix("\n")
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

    /// Create an instance via [`Self::create`], with good defaults.
    pub async fn summon() -> Result<Self, InvocationSummoningError> {
      let python = python::FoundPython::detect().await?;
      let cache_dir = summoning::CacheDir::get_or_create()?;
      let spack_repo = summoning::SpackRepo::summon(cache_dir).await?;
      let spack = Self::create(python, spack_repo).await?;
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
      assert!(spack.version == "0.20.3".to_string());
      Ok(())
    }

    #[tokio::test]
    async fn test_create_invocation() -> Result<(), crate::Error> {
      // Access a few of the relevant files and directories.
      let python = FoundPython::detect().await.unwrap();
      let cache_dir = CacheDir::get_or_create().unwrap();
      let spack_exe = SpackRepo::summon(cache_dir).await.unwrap();
      let spack = SpackInvocation::create(python, spack_exe).await?;

      // This is the current version number for the spack installation.
      assert!(spack.version == "0.20.3".to_string());
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
