/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking spack.

use super::summoning::SpackRepo;

use async_process::Command;
use displaydoc::Display;
use lazy_static::lazy_static;
use regex::Regex;
use signal_hook::consts::{signal::*, TERM_SIGNALS};
use thiserror::Error as ThisError;

use std::{collections::HashMap, io, os::unix::process::ExitStatusExt, process, str};

/// Things that can go wrong when detecting python.
#[derive(Debug, Display, ThisError)]
pub enum PythonError {
  /// unknown error: {0}
  UnknownError(String),
  /// io error: {0}
  Io(#[from] io::Error),
}

/// The executable name we search for on `$PATH` with [Python::detect].
pub const PYTHON_CMD: &str = "python3";
lazy_static! {
  /// Pattern we match against when executing [Python:::detect].
  pub static ref PYTHON_VERSION_REGEX: Regex = Regex::new(r"^Python (3\.[0-9]+\.[0-9]+)\n$").unwrap();
}

/// Refers to a particular python executable [PYTHON_CMD] first on the `$PATH`.
#[derive(Debug, Clone)]
pub struct Python {
  /// Version string parsed from the python executable.
  pub version: String,
}

impl Python {
  /// Check for a valid python installation by parsing the output of `--version`.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// # #[allow(unused_variables)]
  /// let python = spack::invocation::Python::detect().await?;
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub async fn detect() -> Result<Self, PythonError> {
    let process::Output { stdout, stderr, .. } =
      Command::new(PYTHON_CMD).arg("--version").output().await?;
    let stdout = str::from_utf8(&stdout).map_err(|e| {
      PythonError::UnknownError(format!(
        "could not parse utf8 from '{} --version' stdout ({}); received:\n{:?}",
        PYTHON_CMD, &e, &stdout
      ))
    })?;
    match PYTHON_VERSION_REGEX.captures(&stdout) {
      Some(m) => Ok(Self {
        version: m.get(1).unwrap().as_str().to_string(),
      }),
      None => Err(PythonError::UnknownError(format!(
        "could not parse '{} --version'; received:\n(stdout):\n{}\n(stderr):\n{}",
        PYTHON_CMD,
        &stdout,
        str::from_utf8(&stderr).map_err(|e| {
          PythonError::UnknownError(format!(
            "could not parse utf8 from '{} --version' stderr ({}); received:\n{:?}",
            PYTHON_CMD, &e, &stderr
          ))
        })?
      ))),
    }
  }
}

/// Errors that can occur when executing spack.
#[derive(Debug, Display, ThisError)]
pub enum SpackInvocationError {
  /// a spack invocation exited with non-zero status {0}: {1:?}
  NonZeroExit(i32, process::Output),
  /// a spack invocation exited with termination signal {0} ({1}): {2:?}
  ProcessTerminated(i32, &'static str, process::Output),
  /// a spack invocation exited with non-termination signal {0} ({1}): {2:?}
  ProcessKilled(i32, &'static str, process::Output),
  /// unknown error invoking spack: {0}: {1:?}
  UnknownError(String, process::Output),
  /// i/o error invoking spack process: {0}: {1:?}
  Io(#[source] io::Error, process::Output),
}

/// Builder for spack invocations.
#[derive(Debug, Clone)]
pub struct SpackInvocation {
  /// Information about the python executable.
  pub python: Python,
  /// Information about the spack launcher script.
  pub exe: SpackRepo,
  /// Version parsed from executing with '--version'.
  pub version: String,
}

macro_rules! signal_pairs {
  ($($name:ident),+) => {
    [$(($name, stringify!($name))),+]
  }
}

lazy_static! {
  static ref SIGNAL_NAMES: HashMap<i32, &'static str> = HashMap::from(signal_pairs![
    SIGABRT, SIGALRM, SIGBUS, SIGCHLD, SIGCONT, SIGFPE, SIGHUP, SIGILL, SIGINT, SIGIO, SIGKILL,
    SIGPIPE, SIGPROF, SIGQUIT, SIGSEGV, SIGSTOP, SIGSYS, SIGTERM, SIGTRAP, SIGTSTP, SIGTTIN,
    SIGTTOU, SIGURG, SIGUSR1, SIGUSR2, SIGVTALRM, SIGWINCH, SIGXCPU, SIGXFSZ
  ]);
}

impl SpackInvocation {
  /// Create an instance. You should prefer to call .clone() on the first instance you construct.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// # let td = tempdir::TempDir::new("spack-summon-test")?;
  /// # std::env::set_var("HOME", td.path());
  /// use spack::{invocation::{Python, SpackInvocation}, summoning::SpackRepo};
  /// let python = Python::detect().await?;
  /// let spack_exe = SpackRepo::summon().await?;
  /// let spack = SpackInvocation::create(python, spack_exe).await?;
  /// assert!(spack.version == "0.18.0.dev0".to_string());
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub async fn create(python: Python, exe: SpackRepo) -> Result<Self, crate::Error> {
    let mut this = Self {
      python,
      exe,
      version: "".to_string(),
    };
    let output = this.clone().invoke(&["--version".to_string()]).await?;
    this.version = str::from_utf8(&output.stdout)
      .map_err(|e| {
        SpackInvocationError::UnknownError(
          format!(
            "could not parse utf8 from '{} {} --version' stdout ({}); received:\n{:?}",
            PYTHON_CMD,
            this.exe.script_path.display(),
            &e,
            &output.stdout,
          ),
          output.clone(),
        )
      })
      .map_err(|e| crate::Error::Spack(this.clone(), e))?
      .strip_suffix("\n")
      .expect("expected final newline")
      .to_string();
    Ok(this)
  }

  /// Invoke spack as an async process, checking if a Command exited with nonzero.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// # let td = tempdir::TempDir::new("spack-summon-test")?;
  /// # std::env::set_var("HOME", td.path());
  /// use std::{process::Output, str};
  /// use spack::{invocation::{Python, SpackInvocation}, summoning::SpackRepo};
  /// let python = Python::detect().await?;
  /// let spack_exe = SpackRepo::summon().await?;
  /// let spack = SpackInvocation::create(python, spack_exe).await?;
  /// let Output { stdout, .. } = spack.clone().invoke(&["--version".to_string()]).await?;
  /// let version = str::from_utf8(&stdout).unwrap().strip_suffix("\n").unwrap();
  /// assert!(version == &spack.version);
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub async fn invoke(self, args: &[String]) -> Result<process::Output, crate::Error> {
    let output = Command::new(&self.exe.script_path)
      .current_dir(&self.exe.repo_path)
      .env("SPACK_PYTHON", PYTHON_CMD)
      .args(args)
      .output()
      .await?;
    if let Some(code) = output.status.code() {
      if code == 0 {
        Ok(output)
      } else {
        Err(crate::Error::Spack(
          self,
          SpackInvocationError::NonZeroExit(code, output),
        ))
      }
    } else if let Some(signal) = output.status.signal() {
      Err(if TERM_SIGNALS.contains(&signal) {
        crate::Error::Spack(
          self,
          SpackInvocationError::ProcessTerminated(
            signal,
            SIGNAL_NAMES.get(&signal).unwrap(),
            output,
          ),
        )
      } else {
        crate::Error::Spack(
          self,
          SpackInvocationError::ProcessKilled(signal, SIGNAL_NAMES.get(&signal).unwrap(), output),
        )
      })
    } else {
      Err(crate::Error::Spack(
        self,
        SpackInvocationError::UnknownError("no exit code and no signal".to_string(), output),
      ))
    }
  }
}
