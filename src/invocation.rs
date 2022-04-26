/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking spack.

use super::summoning::SpackRepo;

use async_process::{Child, ChildStderr, ChildStdout, Command, Stdio};
use displaydoc::Display;
use futures_lite::{future, io::BufReader, prelude::*};
use lazy_static::lazy_static;
use regex::Regex;
use signal_hook::consts::{signal::*, TERM_SIGNALS};
use thiserror::Error;

use std::{
  collections::HashMap, future::Future, io, os::unix::process::ExitStatusExt, process, str,
};

/// Things that can go wrong when detecting python.
#[derive(Debug, Display, Error)]
pub enum PythonError {
  /// unknown error: {0}
  UnknownError(String),
  /// io error: {0}
  Io(#[from] io::Error),
}

/// The executable name we search for on `$PATH` with [`Python::detect`].
pub const PYTHON_CMD: &str = "python3";
lazy_static! {
  /// Pattern we match against when executing [`Python::detect`].
  pub static ref PYTHON_VERSION_REGEX: Regex = Regex::new(r"^Python (3\.[0-9]+\.[0-9]+)\n$").unwrap();
}

/// Refers to a particular python executable [`PYTHON_CMD`] first on the `$PATH`.
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
#[derive(Debug, Display, Error)]
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
  Io(#[from] io::Error),
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

/// argv=[{0:?}]
#[derive(Debug, Display, Clone, Default)]
pub struct Argv(pub Vec<String>);

impl From<&[&str]> for Argv {
  fn from(value: &[&str]) -> Self {
    Self(value.iter().map(|s| s.to_string()).collect())
  }
}

impl Argv {
  /// Convert to a form suitable for [Invocation::command].
  pub(crate) fn as_strs(&self) -> Vec<&str> {
    self.0.iter().map(|s| s.as_ref()).collect()
  }

  pub(crate) fn trailing_args(self) -> Self {
    if self.0.is_empty() {
      Self(vec![])
    } else {
      Self(
        ["--".to_string()]
          .into_iter()
          .chain(self.0.into_iter())
          .collect(),
      )
    }
  }
}

/// spack invocation {invocation:?} with argv {argv:?} failed: {error}\n(output):\n{output:?}
#[derive(Debug, Display, Error)]
pub struct InvocationErrorWrapper {
  /// Spack and python executable location.
  pub invocation: Invocation,
  /// Arguments passed to the spack script.
  pub argv: Argv,
  /// The output streams of the process execution, if available.
  pub output: Option<process::Output>,
  /// The underlying error.
  #[source]
  pub error: InvocationError,
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
  pub fn analyze_exit_status(
    self,
    argv: Argv,
    output: process::Output,
  ) -> Result<(), InvocationErrorWrapper> {
    Ok(
      {
        if let Some(code) = output.status.code() {
          if code == 0 {
            Ok(())
          } else {
            Err(InvocationError::NonZeroExit(code))
          }
        } else if let Some(signal) = output.status.signal() {
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
      .map_err(|e| InvocationErrorWrapper {
        invocation: self,
        argv,
        output: Some(output),
        error: e,
      })?,
    )
  }

  /// Create an instance.
  ///
  /// You should prefer to call [`Self::clone`] on the first instance you construct instead of
  /// repeatedly calling this method when executing multiple spack invocations in a row.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use spack::{invocation::*, summoning::*};
  ///
  /// // Access a few of the relevant files and directories.
  /// let python = Python::detect().await?;
  /// let cache_dir = CacheDir::get_or_create()?;
  /// let spack_exe = SpackRepo::summon(cache_dir).await?;
  /// let spack = Invocation::create(python, spack_exe).await?;
  ///
  /// // This is the current version number for the spack installation.
  /// assert!(spack.version == "0.18.0.dev0".to_string());
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub async fn create(python: Python, exe: SpackRepo) -> Result<Self, InvocationErrorWrapper> {
    let mut this = Self {
      python,
      exe,
      version: "".to_string(),
    };
    let argv: Argv = ["--version"].as_ref().into();
    let output = this.clone().invoke(argv.clone()).await?;
    this.version = str::from_utf8(&output.stdout)
      .map_err(|e| InvocationErrorWrapper {
        invocation: this.clone(),
        argv,
        output: Some(output.clone()),
        error: InvocationError::UnknownError(format!(
          "could not parse utf8 from '{} {} --version' stdout ({}); received:\n{:?}",
          PYTHON_CMD,
          this.exe.script_path.display(),
          &e,
          &output.stdout,
        )),
      })?
      .strip_suffix("\n")
      .expect("expected final newline")
      .to_string();
    Ok(this)
  }

  fn command(&self, argv: &[&str]) -> Command {
    dbg!(&self.exe);
    dbg!(argv);
    let mut command = Command::new(&self.exe.script_path);
    command
      .current_dir(&self.exe.repo_path)
      .env("SPACK_PYTHON", PYTHON_CMD)
      .args(argv);
    command
  }

  /// Invoke spack as a [`Child`] process and wait on it to complete while slurping its output.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use std::{process::Output, str};
  /// use spack::{invocation::*, summoning::*};
  ///
  /// // Locate executable scripts.
  /// let python = Python::detect().await?;
  /// let cache_dir = CacheDir::get_or_create()?;
  /// let spack_exe = SpackRepo::summon(cache_dir).await?;
  /// let spack = Invocation::create(python, spack_exe).await?;
  ///
  /// // Spawn the child process and wait for it to end.
  /// let Output { stdout, .. } = spack.clone().invoke(["--version"].as_ref().into()).await?;
  /// // Parse stdout into utf8...
  /// let version = str::from_utf8(&stdout).unwrap()
  ///   // ...and strip the trailing newline...
  ///   .strip_suffix("\n").unwrap();
  /// // ...to verify it matches `spack.version`.
  /// assert!(version == &spack.version);
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub async fn invoke(self, argv: Argv) -> Result<process::Output, InvocationErrorWrapper> {
    let output =
      self
        .command(&argv.as_strs())
        .output()
        .await
        .map_err(|e| InvocationErrorWrapper {
          invocation: self.clone(),
          argv: argv.clone(),
          output: None,
          error: InvocationError::Io(e),
        })?;
    self.analyze_exit_status(argv, output.clone())?;
    Ok(output)
  }

  /// Invoke spack as a [`Child`] process, and return a handle to its output streams.
  ///
  /// [`Streaming::stdout`] and [`Streaming::stderr`] can be
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use futures_lite::prelude::*;
  /// use spack::{invocation::*, summoning::*};
  ///
  /// // Locate executable scripts.
  /// let python = Python::detect().await?;
  /// let cache_dir = CacheDir::get_or_create()?;
  /// let spack_exe = SpackRepo::summon(cache_dir).await?;
  /// let spack = Invocation::create(python, spack_exe).await?;
  ///
  /// // Spawn the child process and stream its output, ignoring stderr.
  /// let argv: Argv = ["--version"].as_ref().into();
  /// let Streaming { child, mut stdout, .. } = spack.clone()
  ///   .invoke_streaming(argv.clone())?;
  /// // Slurp stdout all at once into a string.
  /// let mut version: String = "".to_string();
  /// stdout.read_to_string(&mut version).await?;
  /// // Parse the spack version from stdout, and verify it matches `spack.version`.
  /// let version = version.strip_suffix("\n").unwrap();
  /// assert!(version == &spack.version);
  ///
  /// // Now verify the process exited successfully.
  /// let output = child.output().await?;
  /// spack.analyze_exit_status(argv, output)?;
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  pub fn invoke_streaming(self, argv: Argv) -> Result<Streaming, InvocationErrorWrapper> {
    let mut child = self
      .command(&argv.as_strs())
      .stdout(Stdio::piped())
      .stderr(Stdio::piped())
      .spawn()
      .map_err(|e| InvocationErrorWrapper {
        invocation: self.clone(),
        argv: argv.clone(),
        output: None,
        error: InvocationError::Io(e),
      })?;
    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();
    Ok(Streaming {
      child,
      stdout,
      stderr,
      spack: self.clone(),
      argv: argv.clone(),
    })
  }
}

/// A handle to the result of [`Invocation::invoke_streaming`].
pub struct Streaming {
  /// The handle to the live child process (live until [`Child::output`] is called).
  pub child: Child,
  /// The stdout stream, separated from the process handle.
  pub stdout: ChildStdout,
  /// The stderr stream, separated from the process handler.
  pub stderr: ChildStderr,
  /// The locations of the python and spack scripts.
  pub spack: Invocation,
  /// The argv this process was executed with.
  pub argv: Argv,
}

impl Streaming {
  pub(crate) async fn exhaust_output_streams_and_wait<E, F>(
    self,
    act: fn(StdioLine) -> F,
  ) -> Result<(), InvocationErrorWrapper>
  where
    InvocationError: From<E>,
    F: Future<Output = Result<(), E>>,
  {
    let Self {
      stdout,
      stderr,
      child,
      spack,
      argv,
    } = self;
    /* stdout wrapping. */
    let mut out_lines = BufReader::new(stdout).lines();
    /* stderr wrapping. */
    let mut err_lines = BufReader::new(stderr).lines();

    /* Crossing the streams!!! */
    let output = async move {
      while let Some(line) =
        StdioLine::merge_streams(out_lines.next().boxed(), err_lines.next().boxed())
          .await
          .map_err(|e| InvocationError::Io(e))?
      {
        act(line).await.map_err(InvocationError::from)?;
      }
      let output = child.output().await.map_err(InvocationError::Io)?;
      Ok(output)
    }
    .await
    .map_err(|e| InvocationErrorWrapper {
      invocation: spack.clone(),
      argv: argv.clone(),
      output: None,
      error: e,
    })?;

    spack.analyze_exit_status(argv.clone(), output)?;
    Ok(())
  }
}

/// A line of either stdout or stderr from a subprocess.
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
          Ok(line) => Ok(Some(Self::Err(line))),
          Err(e) => Err(e),
        },
        None => Ok(None),
      }
    };
    let out = async move {
      match out.await {
        Some(line) => match line {
          Ok(line) => Ok(Some(Self::Out(line))),
          Err(e) => Err(e),
        },
        None => Ok(None),
      }
    };
    future::or(err, out)
  }
}
