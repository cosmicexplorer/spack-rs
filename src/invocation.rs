/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking spack.

use super::summoning::SpackRepo;

use async_process::{Child, ChildStderr, ChildStdout, Command, Stdio};
use displaydoc::Display;
use futures_lite::future;
use lazy_static::lazy_static;
use regex::Regex;
use signal_hook::consts::{signal::*, TERM_SIGNALS};
use thiserror::Error as ThisError;

use std::{
  collections::HashMap, future::Future, io, os::unix::process::ExitStatusExt, process, str,
};

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
pub enum InvocationError {
  /// a spack invocation exited with non-zero status {0}
  NonZeroExit(i32),
  /// a spack invocation exited with termination signal {0} ({1})
  ProcessTerminated(i32, &'static str),
  /// a spack invocation exited with non-termination signal {0} ({1})
  ProcessKilled(i32, &'static str),
  /// unknown error invoking spack: {0}
  UnknownError(String),
  /// i/o error invoking spack process: {0}
  Io(#[source] io::Error),
}

/// Builder for spack invocations.
#[derive(Debug, Clone)]
pub struct Invocation {
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

impl Invocation {
  /// Raise an error if the process exited with any type of failure.
  pub fn analyze_exit_status(status: &process::ExitStatus) -> Result<(), InvocationError> {
    if let Some(code) = status.code() {
      if code == 0 {
        Ok(())
      } else {
        Err(InvocationError::NonZeroExit(code))
      }
    } else if let Some(signal) = status.signal() {
      Err(if TERM_SIGNALS.contains(&signal) {
        InvocationError::ProcessTerminated(signal, SIGNAL_NAMES.get(&signal).unwrap())
      } else {
        InvocationError::ProcessKilled(signal, SIGNAL_NAMES.get(&signal).unwrap())
      })
    } else {
      Err(InvocationError::UnknownError(
        "no exit code and no signal".to_string(),
      ))
    }
  }

  /// Create an instance. You should prefer to call .clone() on the first instance you construct.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use spack::{invocation::{Python, Invocation}, summoning::SpackRepo};
  /// let python = Python::detect().await?;
  /// let spack_exe = SpackRepo::summon().await?;
  /// let spack = Invocation::create(python, spack_exe).await?;
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
    let output = this.clone().invoke(&["--version"]).await?;
    this.version = str::from_utf8(&output.stdout)
      .map_err(|e| {
        InvocationError::UnknownError(format!(
          "could not parse utf8 from '{} {} --version' stdout ({}); received:\n{:?}",
          PYTHON_CMD,
          this.exe.script_path.display(),
          &e,
          &output.stdout,
        ))
      })
      .map_err(|e| crate::Error::Invocation(this.clone(), output.clone(), e))?
      .strip_suffix("\n")
      .expect("expected final newline")
      .to_string();
    Ok(this)
  }

  fn command(&self, args: &[&str]) -> Command {
    let mut command = Command::new(&self.exe.script_path);
    command
      .current_dir(&self.exe.repo_path)
      .env("SPACK_PYTHON", PYTHON_CMD)
      .args(args);
    command
  }

  /// Invoke spack as an async process, checking if a Command exited with nonzero.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use std::{process::Output, str};
  /// use spack::{invocation::{Python, Invocation}, summoning::SpackRepo};
  /// let python = Python::detect().await?;
  /// let spack_exe = SpackRepo::summon().await?;
  /// let spack = Invocation::create(python, spack_exe).await?;
  /// let Output { stdout, .. } = spack.clone().invoke(&["--version"]).await?;
  /// let version = str::from_utf8(&stdout).unwrap().strip_suffix("\n").unwrap();
  /// assert!(version == &spack.version);
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub async fn invoke(self, args: &[&str]) -> Result<process::Output, crate::Error> {
    let output = self.command(args).output().await?;
    Self::analyze_exit_status(&output.status)
      .map_err(|e| crate::Error::Invocation(self, output.clone(), e))?;
    Ok(output)
  }

  /// Invoke spack as an async process, streaming its stdout.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use futures_lite::prelude::*;
  /// use spack::{invocation::*, summoning::SpackRepo};
  /// let python = Python::detect().await?;
  /// let spack_exe = SpackRepo::summon().await?;
  /// let spack = Invocation::create(python, spack_exe).await?;
  /// let Streaming { child, mut stdout, .. } = spack.clone().invoke_streaming(&["--version"])?;
  /// let mut version: String = "".to_string();
  /// stdout.read_to_string(&mut version).await?;
  /// let version = version.strip_suffix("\n").unwrap();
  /// assert!(version == &spack.version);
  /// let output = child.output().await?;
  /// Invocation::analyze_exit_status(&output.status)
  ///   .map_err(|e| spack::Error::Invocation(spack, output, e))?;
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub fn invoke_streaming(self, args: &[&str]) -> Result<Streaming, crate::Error> {
    let mut child = self
      .command(args)
      .stdout(Stdio::piped())
      .stderr(Stdio::piped())
      .spawn()?;
    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();
    Ok(Streaming {
      child,
      stdout,
      stderr,
    })
  }
}

/// A handle to the result of [Invocation::invoke_streaming].
pub struct Streaming {
  /// The handle to the live child process (live until [Child::output] is called).
  pub child: Child,
  /// The stdout stream, separated from the process handle.
  pub stdout: ChildStdout,
  /// The stderr stream, separated from the process handler.
  pub stderr: ChildStderr,
}

/// A line of either stdout or stderr from a subprocess.
#[allow(missing_docs)]
pub(crate) enum StdioLine {
  Out(String),
  Err(String),
}

impl StdioLine {
  /// Select on both stdout and stderr, with preference given to stderr if both are ready.
  pub fn merge_streams<F>(out: F, err: F) -> impl Future<Output = io::Result<Option<Self>>>
  where
    F: Future<Output = Option<io::Result<String>>>,
  {
    let err = async move {
      match err.await {
        Some(line) => match line {
          Ok(line) => Ok(Some(StdioLine::Err(line))),
          Err(e) => Err(e),
        },
        None => Ok(None),
      }
    };
    let out = async move {
      match out.await {
        Some(line) => match line {
          Ok(line) => Ok(Some(StdioLine::Out(line))),
          Err(e) => Err(e),
        },
        None => Ok(None),
      }
    };
    future::or(err, out)
  }
}
