/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking spack.

pub mod command {
  use displaydoc::Display;
  use lazy_static::lazy_static;
  use signal_hook::consts::{signal::*, TERM_SIGNALS};
  use thiserror::Error;

  use std::{collections::HashMap, io, os::unix::process::ExitStatusExt, path::PathBuf, process};

  /// argv=[{0:?}]
  #[derive(Debug, Display, Clone, Default)]
  pub struct Argv(pub Vec<String>);

  impl From<&[&str]> for Argv {
    fn from(value: &[&str]) -> Self {
      Self(value.iter().map(|s| s.to_string()).collect())
    }
  }

  impl Argv {
    /* FIXME: make this return a Result<(), CommandValidationError> with new validation error type! */
    /// Assert that this command has no additional arguments, and drop `self`.
    pub fn drop_empty(self) {
      assert!(self.0.is_empty());
    }

    pub fn empty() -> Self {
      Self(Vec::new())
    }

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

  /// Execute a process asynchronously.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use std::str;
  /// use futures_lite::io::AsyncReadExt;
  /// use spack::invocation::{
  ///   command::{self, CommandBase, sync::{Output, SyncInvocable}, stream::Streamable},
  ///   spack::Invocation,
  /// };
  ///
  /// // Locate executable scripts.
  /// let spack = Invocation::summon().await.unwrap();
  ///
  /// let argv: command::Argv = ["--version"].as_ref().into();
  ///
  /// // Spawn the child process and wait for it to end.
  /// let command = spack.clone().hydrate_command(argv.clone()).unwrap();
  /// let Output { stdout } = command.clone().invoke().await.expect("sync invocation failed");
  /// // Parse stdout into utf8...
  /// let version = str::from_utf8(&stdout).unwrap()
  ///   // ...and strip the trailing newline...
  ///   .strip_suffix("\n").unwrap();
  /// // ...to verify it matches `spack.version`.
  /// assert!(version == &spack.version);
  ///
  /// // Spawn the child process and stream its output, ignoring stderr.
  /// let mut streaming = command.invoke_streaming().expect("streaming invocation failed");
  /// // Slurp stdout all at once into a string.
  /// let mut version: String = "".to_string();
  /// streaming.stdout.read_to_string(&mut version).await.expect("reading stdout failed");
  /// // Parse the spack version from stdout, and verify it matches `spack.version`.
  /// let version = version.strip_suffix("\n").unwrap();
  /// assert!(version == &spack.version);
  ///
  /// // Now verify the process exited successfully.
  /// streaming.wait().await.expect("streaming command should have succeeded");
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  #[derive(Debug, Clone)]
  pub struct Command {
    /// Executable name, which may be absolute or relative to `$PATH` entries.
    pub exe: PathBuf,
    /// The working directory for the child process; otherwise, the working directory is inherited
    /// from the parent process.
    pub wd: Option<PathBuf>,
    /// Arguments to pass to the executable. These should *not* be quoted at all.
    pub argv: Argv,
    /// Any extra environment variables to set within the child process. The environment is
    /// otherwise inherited from the parent.
    pub env: HashMap<String, String>,
  }

  impl Default for Command {
    fn default() -> Self {
      Self {
        exe: PathBuf::from(""),
        wd: None,
        argv: Argv::empty(),
        env: HashMap::new(),
      }
    }
  }

  impl Command {
    fn command(self) -> async_process::Command {
      dbg!(&self);
      let Self { exe, wd, argv, env } = self;
      let mut command = async_process::Command::new(exe);
      if let Some(wd) = wd {
        command.current_dir(wd);
      }
      command.args(&argv.as_strs());
      for (var, val) in env.into_iter() {
        command.env(&var, &val);
      }
      command
    }
  }

  /// Declare higher-level operations which desugar to command lines by implementing this trait.
  pub trait CommandBase {
    /* FIXME: make this return a Result<_, CommandValidationError> with new validation error type! */
    /// Given a list of positional arguments, generate a command line which may or may not
    /// incorporate those additional arguments.
    fn hydrate_command(self, argv: Argv) -> Result<Command, CommandErrorWrapper>;
  }

  /// Errors that can occur when executing command lines.
  #[derive(Debug, Display, Error)]
  pub enum CommandError {
    /// a command line exited with non-zero status {0}
    NonZeroExit(i32),
    /// a command line exited with termination signal {0} ({1})
    ProcessTerminated(i32, &'static str),
    /// a command line exited with non-termination signal {0} ({1})
    ProcessKilled(i32, &'static str),
    /// unknown error from command line: {0}
    UnknownError(String),
    /// i/o error invoking command line: {0}
    Io(#[from] io::Error),
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

  impl CommandError {
    /// Raise an error if the process exited with any type of failure.
    pub fn analyze_exit_status(status: process::ExitStatus) -> Result<(), Self> {
      if let Some(code) = status.code() {
        if code == 0 {
          Ok(())
        } else {
          Err(Self::NonZeroExit(code))
        }
      } else if let Some(signal) = status.signal() {
        Err(if TERM_SIGNALS.contains(&signal) {
          Self::ProcessTerminated(signal, SIGNAL_NAMES.get(&signal).unwrap())
        } else {
          Self::ProcessKilled(signal, SIGNAL_NAMES.get(&signal).unwrap())
        })
      } else {
        Err(Self::UnknownError("no exit code and no signal".to_string()))
      }
    }
  }

  /// command {command:?} failed: {error}\n(output):\n{output:?}
  #[derive(Debug, Display, Error)]
  pub struct CommandErrorWrapper {
    /// The command that attempted to be executed.
    pub command: Command,
    /// The output streams of the process execution, if available.
    pub output: Option<sync::Output>,
    /// The underlying error.
    #[source]
    pub error: CommandError,
  }

  pub mod sync {
    use super::*;

    use async_trait::async_trait;

    use std::{
      io::{self, Write},
      process,
    };

    #[async_trait]
    pub trait SyncInvocable {
      /// Invoke a child process and wait on it to complete while slurping its output.
      async fn invoke(self) -> Result<Output, CommandErrorWrapper>;
    }

    #[derive(Debug, Clone)]
    pub struct Output {
      pub stdout: Vec<u8>,
    }

    impl Output {
      fn propagate_stderr(err_out: Vec<u8>) -> io::Result<()> {
        let stderr = io::stderr();
        let mut handle = stderr.lock();
        handle.write_all(&err_out)?;
        handle.flush()?;
        Ok(())
      }

      pub fn extract(
        command: Command,
        output: process::Output,
      ) -> Result<Self, CommandErrorWrapper> {
        let process::Output {
          status,
          stdout,
          stderr,
        } = output;

        let output = Self { stdout };
        Self::propagate_stderr(stderr)
          .map_err(CommandError::Io)
          .and_then(|()| CommandError::analyze_exit_status(status))
          .map_err(|e| CommandErrorWrapper {
            command,
            output: Some(output.clone()),
            error: e,
          })?;

        Ok(output)
      }
    }

    #[async_trait]
    impl SyncInvocable for Command {
      async fn invoke(self) -> Result<Output, CommandErrorWrapper> {
        let mut command = self.clone().command();
        let output = command.output().await.map_err(|e| CommandErrorWrapper {
          command: self.clone(),
          output: None,
          error: e.into(),
        })?;
        let output = Output::extract(self, output)?;
        Ok(output)
      }
    }
  }

  pub mod stream {
    use super::*;

    use async_process::{self, Child, ChildStderr, ChildStdout, Stdio};
    use futures_lite::{future, io::BufReader, prelude::*};

    use std::{future::Future, io};

    pub trait Streamable {
      /// Invoke a child process and return a handle to its output streams.
      fn invoke_streaming(self) -> Result<Streaming, CommandErrorWrapper>;
    }

    /// A handle to the result of [`Invocation::invoke_streaming`].
    pub struct Streaming {
      /// The handle to the live child process (live until [`Child::output`] is called).
      pub child: Child,
      /// The stdout stream, separated from the process handle.
      pub stdout: ChildStdout,
      /// The stderr stream, separated from the process handler.
      pub stderr: ChildStderr,
      /// The command being executed.
      pub command: Command,
    }

    impl Streaming {
      pub async fn exhaust_output_streams_and_wait<E, F>(
        self,
        act: fn(StdioLine) -> F,
      ) -> Result<(), CommandErrorWrapper>
      where
        CommandError: From<E>,
        F: Future<Output = Result<(), E>>,
      {
        let Self {
          stdout,
          stderr,
          mut child,
          command,
        } = self;
        /* stdout wrapping. */
        let mut out_lines = BufReader::new(stdout).lines();
        /* stderr wrapping. */
        let mut err_lines = BufReader::new(stderr).lines();

        /* Crossing the streams!!! */
        let status = async move {
          while let Some(line) =
            StdioLine::merge_streams(out_lines.next().boxed(), err_lines.next().boxed())
              .await
              .map_err(|e| CommandError::Io(e))?
          {
            act(line).await.map_err(CommandError::from)?;
          }
          let output = child.status().await.map_err(CommandError::Io)?;
          Ok(output)
        }
        .await
        .map_err(|e| CommandErrorWrapper {
          command: command.clone(),
          output: None,
          error: e,
        })?;

        CommandError::analyze_exit_status(status).map_err(|e| CommandErrorWrapper {
          command,
          output: None,
          error: e,
        })?;
        Ok(())
      }

      /// Copy over all stderr lines to our stderr, and stdout lines to our stdout.
      async fn stdio_streams_callback(line: StdioLine) -> Result<(), CommandError> {
        match line {
          StdioLine::Err(err) => {
            eprintln!("{}", err);
          }
          StdioLine::Out(out) => {
            println!("{}", out);
          }
        }
        Ok(())
      }

      pub async fn wait(self) -> Result<(), CommandErrorWrapper> {
        self
          .exhaust_output_streams_and_wait(Self::stdio_streams_callback)
          .await
      }
    }

    /// A line of either stdout or stderr from a subprocess.
    pub enum StdioLine {
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

    impl Streamable for Command {
      fn invoke_streaming(self) -> Result<Streaming, CommandErrorWrapper> {
        let mut command = self.clone().command();
        let mut child = command
          .stdout(Stdio::piped())
          .stderr(Stdio::piped())
          .spawn()
          .map_err(|e| CommandErrorWrapper {
            command: self.clone(),
            output: None,
            error: CommandError::Io(e),
          })?;
        let stdout = child.stdout.take().unwrap();
        let stderr = child.stderr.take().unwrap();
        Ok(Streaming {
          child,
          stdout,
          stderr,
          command: self,
        })
      }
    }
  }
}

pub mod python {
  use super::command::{sync::*, *};

  use displaydoc::Display;
  use lazy_static::lazy_static;
  use regex::Regex;
  use thiserror::Error;

  use std::{collections::HashMap, io, path::PathBuf, str};

  /// Things that can go wrong when detecting python.
  #[derive(Debug, Display, Error)]
  pub enum PythonError {
    /// unknown error: {0}
    UnknownError(String),
    /// {0}
    Command(#[from] CommandErrorWrapper),
    /// io error: {0}
    Io(#[from] io::Error),
  }

  /// The executable name we search for on `$PATH` with [`Python::detect`].
  pub(crate) const PYTHON_CMD: &str = "python3";
  lazy_static! {
    /// Pattern we match against when executing [`Python::detect`].
    static ref PYTHON_VERSION_REGEX: Regex = Regex::new(r"^Python (3\.[0-9]+\.[0-9]+)\n$").unwrap();
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
    /// let python = spack::invocation::python::Python::detect().await.unwrap();
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn detect() -> Result<Self, PythonError> {
      let command = Command {
        exe: PathBuf::from(PYTHON_CMD),
        wd: None,
        argv: ["--version"].as_ref().into(),
        env: HashMap::new(),
      };
      let Output { stdout } = command.invoke().await?;
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
          "could not parse '{} --version'; received:\n(stdout):\n{}",
          PYTHON_CMD, &stdout,
        ))),
      }
    }
  }
}

pub mod spack {
  use super::{
    command::{self, sync::SyncInvocable, CommandBase},
    python,
  };
  use crate::summoning;

  use displaydoc::Display;
  use thiserror::Error;

  use std::{io, str};

  #[derive(Debug, Display, Error)]
  pub enum InvocationSummoningError {
    /// error executing command: {0}
    Command(#[from] command::CommandErrorWrapper),
    /// error summoning: {0}
    Summon(#[from] summoning::SummoningError),
    /// error location python: {0}
    Python(#[from] python::PythonError),
    /// io error: {0}
    Io(#[from] io::Error),
  }

  /// Builder for spack invocations.
  #[derive(Debug, Clone)]
  pub struct Invocation {
    /// Information about the python executable.
    pub python: python::Python,
    /// Information about the spack launcher script.
    pub exe: summoning::SpackRepo,
    /// Version parsed from executing with '--version'.
    pub version: String,
  }

  impl command::CommandBase for Invocation {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      let Self { exe, .. } = self;
      Ok(command::Command {
        exe: exe.script_path,
        wd: Some(exe.repo_path),
        argv,
        env: [("SPACK_PYTHON", python::PYTHON_CMD)]
          .into_iter()
          .map(|(k, v)| (k.to_string(), v.to_string()))
          .collect(),
      })
    }
  }

  impl Invocation {
    /// Create an instance.
    ///
    /// You should prefer to call [`Self::clone`] on the first instance you construct instead of
    /// repeatedly calling this method when executing multiple spack invocations in a row.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{invocation::{python::*, spack::*}, summoning::*};
    ///
    /// // Access a few of the relevant files and directories.
    /// let python = Python::detect().await.unwrap();
    /// let cache_dir = CacheDir::get_or_create().unwrap();
    /// let spack_exe = SpackRepo::summon(cache_dir).await.unwrap();
    /// let spack = Invocation::create(python, spack_exe).await.expect("creation should succeed");
    ///
    /// // This is the current version number for the spack installation.
    /// assert!(spack.version == "0.18.0.dev0".to_string());
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn create(
      python: python::Python,
      exe: summoning::SpackRepo,
    ) -> Result<Self, command::CommandErrorWrapper> {
      let mut this = Self {
        python,
        exe,
        version: "".to_string(),
      };
      let argv: command::Argv = ["--version"].as_ref().into();
      let command = this.clone().hydrate_command(argv)?;
      let output = command.clone().invoke().await?;
      this.version = str::from_utf8(&output.stdout)
        .map_err(|e| command::CommandErrorWrapper {
          command,
          output: Some(output.clone()),
          error: command::CommandError::UnknownError(format!(
            "could not parse utf8 from '{} {} --version' stdout: {}",
            python::PYTHON_CMD,
            this.exe.script_path.display(),
            &e,
          )),
        })?
        .strip_suffix("\n")
        .expect("expected final newline")
        .to_string();
      Ok(this)
    }

    /// Create an instance via [`Self::create`], with good defaults.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::invocation::spack::Invocation;
    ///
    /// let spack = Invocation::summon().await?;
    /// // This is the current version number for the spack installation.
    /// assert!(spack.version == "0.18.0.dev0".to_string());
    /// # Ok(())
    /// # }) // async
    /// # }
    pub async fn summon() -> Result<Self, InvocationSummoningError> {
      let python = python::Python::detect().await?;
      let cache_dir = summoning::CacheDir::get_or_create()?;
      let spack_repo = summoning::SpackRepo::summon(cache_dir).await?;
      let spack = Self::create(python, spack_repo).await?;
      Ok(spack)
    }
  }
}

pub mod env {
  use super::{
    command::{self, CommandBase},
    spack,
  };

  use tempfile::{NamedTempFile, TempPath};

  use std::{
    io::{self, Write},
    path::{Path, PathBuf},
  };

  /// A source-able script to handle the result of [`Load::load`].
  #[derive(Debug, Clone)]
  pub struct LoadEnvironment(pub String);

  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use std::str;
  /// use spack::{
  ///   commands::{*, install::*, load::*},
  ///   invocation::{spack::Invocation, env::*, command::{*, sync::{Output, SyncInvocable}}},
  /// };
  ///
  /// let spack = Invocation::summon().await?;
  ///
  /// // Ensure a python is installed that is at least version 3.
  /// let install = Install { spack: spack.clone(), spec: CLISpec::new("python@3:") };
  /// let found_py_spec = install.clone().install_find().await.unwrap();
  ///
  /// // Look for a python spec with that exact hash.
  /// let load = Load { spack: spack.clone(), specs: vec![found_py_spec.hashed_spec()] };
  /// let python_env = load.clone().load().await.expect("load command failed");
  ///
  /// let env_spack = EnvInvocation {
  ///   inner: spack.clone(),
  ///   load_env: python_env,
  /// };
  /// let command = env_spack.hydrate_command(["--version"].as_ref().into())
  ///   .expect("env wrapping failed");
  /// let Output { stdout } = command.invoke().await.expect("version command failed");
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
  #[derive(Debug, Clone)]
  pub struct EnvInvocation {
    pub inner: spack::Invocation,
    pub load_env: LoadEnvironment,
  }

  impl EnvInvocation {
    fn write_env_script(exe: &Path, load_env: LoadEnvironment) -> io::Result<TempPath> {
      /* Create the script. */
      let (mut script_file, script_path) = NamedTempFile::new()?.into_parts();
      let runner_script_contents = format!(
        "{}\n\nexec {} $@\n",
        load_env.0,
        shlex::quote(&format!("{}", exe.display()))
      );
      script_file.write_all(runner_script_contents.as_bytes())?;
      script_file.sync_all()?;
      /* Close the file, but keep the path alive. */
      Ok(script_path)
    }
  }

  impl CommandBase for EnvInvocation {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      eprintln!("EnvInvocation");
      dbg!(&self);
      dbg!(&argv);
      let Self { inner, load_env } = self;

      /* Create the script. */
      let command = inner.clone().hydrate_command(argv.clone())?;
      let script_path = Self::write_env_script(&inner.exe.script_path, load_env).map_err(|e| {
        command::CommandErrorWrapper {
          command,
          output: None,
          error: e.into(),
        }
      })?;

      /* Craft the command line. */
      let argv = command::Argv(
        [format!("{}", script_path.display())]
          .into_iter()
          .chain(argv.0.into_iter())
          .collect(),
      );
      let mut command = inner.hydrate_command(argv)?;
      command.exe = PathBuf::from("sh");

      /* FIXME: We don't ever delete the script! */
      script_path.keep().unwrap();

      Ok(command)
    }
  }
}
