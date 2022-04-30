/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

pub mod fs {
  use displaydoc::Display;

  use std::path::PathBuf;

  /// @={0}
  ///
  /// FIXME
  #[derive(Debug, Display, Clone)]
  #[ignore_extra_doc_attributes]
  pub struct File(pub PathBuf);

  impl File {
    pub fn into_path_buf(self) -> PathBuf {
      let Self(path) = self;
      path
    }
  }

  /// @<{0}
  ///
  /// FIXME
  #[derive(Debug, Display, Clone)]
  #[ignore_extra_doc_attributes]
  pub struct Directory(pub PathBuf);

  impl Directory {
    pub fn into_path_buf(self) -> PathBuf {
      let Self(path) = self;
      path
    }
  }
}

pub mod exe {
  use super::fs;

  use displaydoc::Display;
  use indexmap::IndexMap;
  use lazy_static::lazy_static;
  use signal_hook::consts::{signal::*, TERM_SIGNALS};
  use thiserror::Error;

  use std::{
    ffi::{OsStr, OsString},
    io, iter,
    os::unix::process::ExitStatusExt,
    path::{Path, PathBuf},
    process, str,
  };

  /// *{0}
  ///
  /// FIXME
  #[derive(Debug, Display, Clone)]
  #[ignore_extra_doc_attributes]
  pub struct Exe(pub fs::File);

  impl<R: AsRef<OsStr>> From<&R> for Exe {
    fn from(value: &R) -> Self {
      let p = Path::new(value);
      let f = fs::File(p.to_path_buf());
      Self(f)
    }
  }

  impl Default for Exe {
    fn default() -> Self {
      Self(fs::File(PathBuf::default()))
    }
  }

  impl Exe {
    pub fn is_empty(&self) -> bool {
      let Self(fs::File(exe)) = self;
      exe.as_os_str().is_empty()
    }

    pub fn into_path_buf(self) -> PathBuf {
      let Self(exe) = self;
      exe.into_path_buf()
    }
  }

  /// [{0:?}]
  ///
  /// FIXME
  #[derive(Debug, Display, Clone, Default)]
  #[ignore_extra_doc_attributes]
  pub struct Argv(pub Vec<OsString>);

  impl<R: AsRef<OsStr>, I: iter::IntoIterator<Item = R>> From<I> for Argv {
    fn from(value: I) -> Self {
      let argv: Vec<OsString> = value
        .into_iter()
        .map(|s| {
          let s: &OsStr = s.as_ref();
          s.to_os_string()
        })
        .collect();
      Self(argv)
    }
  }

  impl Argv {
    pub(crate) fn trailing_args(self) -> Self {
      let Self(argv) = self;
      if argv.is_empty() {
        Self(vec![])
      } else {
        Self(["--".into()].into_iter().chain(argv.into_iter()).collect())
      }
    }

    pub fn unshift(&mut self, leftmost_arg: OsString) {
      let mut ret = vec![leftmost_arg];
      let Self(ref mut argv) = self;
      ret.extend(argv.clone());
      *argv = ret;
    }
  }

  /// [{0:?}]
  ///
  /// FIXME
  #[derive(Debug, Display, Clone, Default)]
  #[ignore_extra_doc_attributes]
  pub struct EnvModifications(pub IndexMap<OsString, OsString>);

  impl<R: AsRef<OsStr>, I: iter::IntoIterator<Item = (R, R)>> From<I> for EnvModifications {
    fn from(value: I) -> Self {
      let env: IndexMap<OsString, OsString> = value
        .into_iter()
        .map(|(k, v)| {
          let k: &OsStr = k.as_ref();
          let v: &OsStr = v.as_ref();
          (k.to_os_string(), v.to_os_string())
        })
        .collect();
      Self(env)
    }
  }

  /// <exe={exe}, wd={wd:?}, argv={argv}, env={env}>
  ///
  /// Request to execute a subprocess.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use std::{str, path::PathBuf};
  /// use futures_lite::io::AsyncReadExt;
  /// use spack::subprocess::{fs, exe, sync::SyncInvocable, stream::Streamable};
  ///
  /// let command = exe::Command {
  ///   exe: exe::Exe(fs::File(PathBuf::from("echo"))),
  ///   argv: ["hey"].as_ref().into(),
  ///   ..Default::default()
  /// };
  ///
  /// // Spawn the child process and wait for it to end.
  /// let output = command.clone().invoke().await.expect("sync subprocess failed");
  /// // Parse stdout into utf8...
  /// let hey = str::from_utf8(&output.stdout).expect("utf8 decoding failed")
  ///   // ...and strip the trailing newline.
  ///   .strip_suffix("\n")
  ///   .expect("trailing newline not found");
  /// assert!(hey == "hey");
  ///
  /// // Spawn the child process and stream its output, ignoring stderr for now.
  /// let mut streaming = command.invoke_streaming().expect("streaming subprocess failed");
  /// // Slurp stdout all at once into a string.
  /// let mut out: String = "".to_string();
  /// streaming.stdout.read_to_string(&mut out).await.expect("reading stdout failed");
  ///
  /// // Now verify the process exited successfully.
  /// streaming.wait().await.expect("streaming command should have succeeded");
  ///
  /// // Validate we get the same output streaming.
  /// let hey = out.strip_suffix("\n").unwrap();
  /// assert!(hey == "hey");
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  #[derive(Debug, Display, Clone, Default)]
  #[ignore_extra_doc_attributes]
  pub struct Command {
    /// Executable name, which may be absolute or relative to `$PATH` entries.
    pub exe: Exe,
    /// The working directory for the child process; otherwise, the working directory is inherited
    /// from the parent process.
    pub wd: Option<fs::Directory>,
    /// Arguments to pass to the executable. These should *not* be quoted at all.
    pub argv: Argv,
    /// Any new environment variables to set within the child process. The environment is
    /// otherwise inherited from the parent.
    pub env: EnvModifications,
  }

  impl Command {
    pub(super) fn command(self) -> async_process::Command {
      dbg!(&self);
      let Self {
        exe,
        wd,
        argv,
        env: EnvModifications(env),
      } = self;
      if exe.is_empty() {
        unreachable!(
          "command was executed before .exe was set; this can only occur using ::default()"
        );
      }
      let mut command = async_process::Command::new(exe.into_path_buf());
      if let Some(wd) = wd {
        command.current_dir(wd.into_path_buf());
      }
      command.args(argv.0);
      for (var, val) in env.into_iter() {
        command.env(&var, &val);
      }
      command
    }

    pub(crate) fn unshift_new_exe(&mut self, new_exe: Exe) {
      if new_exe.is_empty() {
        unreachable!("new_exe is an empty string!! self was: {:?}", self);
      }

      let mut argv = self.argv.clone();
      if !self.exe.is_empty() {
        argv.unshift(self.exe.clone().into_path_buf().as_os_str().to_os_string());
      }

      self.argv = argv;
      self.exe = new_exe;
    }

    pub(crate) fn unshift_shell_script(&mut self, script_path: Exe) {
      self.unshift_new_exe(script_path);
      self.unshift_new_exe(Exe(fs::File(PathBuf::from("sh"))));
    }
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
    /// i/o error invoking command line: {0}
    Io(#[from] io::Error),
    /// utf-8 decoding error for command line: {0}
    Utf8(#[from] str::Utf8Error),
  }

  macro_rules! signal_pairs {
  ($($name:ident),+) => {
    [$(($name, stringify!($name))),+]
  }
  }

  lazy_static! {
    static ref SIGNAL_NAMES: IndexMap<i32, &'static str> = signal_pairs![
      SIGABRT, SIGALRM, SIGBUS, SIGCHLD, SIGCONT, SIGFPE, SIGHUP, SIGILL, SIGINT, SIGIO, SIGKILL,
      SIGPIPE, SIGPROF, SIGQUIT, SIGSEGV, SIGSTOP, SIGSYS, SIGTERM, SIGTRAP, SIGTSTP, SIGTTIN,
      SIGTTOU, SIGURG, SIGUSR1, SIGUSR2, SIGVTALRM, SIGWINCH, SIGXCPU, SIGXFSZ
    ]
    .into();
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
        unreachable!("status {:?} had no exit code or signal", status)
      }
    }

    pub fn command_with_context(self, command: Command, context: String) -> CommandErrorWrapper {
      CommandErrorWrapper {
        command,
        context,
        error: self,
      }
    }
  }

  /// command {command:?} failed ({context}): {error}
  #[derive(Debug, Display, Error)]
  pub struct CommandErrorWrapper {
    /// The command that attempted to be executed.
    pub command: Command,
    pub context: String,
    /// The underlying error.
    #[source]
    pub error: CommandError,
  }
}

pub mod base {
  use super::*;

  use async_trait::async_trait;
  use displaydoc::Display;
  use thiserror::Error;

  use std::io;

  /// Errors which may occur during the execution of [`CommandBase::setup_command`].
  #[derive(Debug, Display, Error)]
  pub enum SetupError {
    /// inner error: {0}
    Inner(#[source] Box<SetupErrorWrapper>),
    /// i/o error: {0}
    Io(#[from] io::Error),
  }

  impl SetupError {
    pub fn with_context(self, context: String) -> SetupErrorWrapper {
      SetupErrorWrapper {
        context,
        error: self,
      }
    }
  }

  /// setup error ({context}): {error}
  #[derive(Debug, Display, Error)]
  pub struct SetupErrorWrapper {
    pub context: String,
    #[source]
    pub error: SetupError,
  }

  /// Declare higher-level operations which desugar to command lines by implementing this trait.
  #[async_trait]
  pub trait CommandBase {
    /// Generate a command line from the given object.
    async fn setup_command(self) -> Result<exe::Command, SetupError>;
  }
}

pub mod sync {
  use super::exe;

  use async_trait::async_trait;

  use std::{process, str};

  #[derive(Debug, Clone)]
  pub struct RawOutput {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
  }

  impl RawOutput {
    pub(crate) fn extract(
      command: exe::Command,
      output: process::Output,
    ) -> Result<Self, exe::CommandErrorWrapper> {
      let process::Output {
        status,
        stdout,
        stderr,
      } = output;

      let output = Self { stdout, stderr };
      exe::CommandError::analyze_exit_status(status).map_err(|e| {
        let output_msg: String = match output.clone().decode(command.clone()) {
          Ok(decoded) => format!("(utf-8 decoded) {:?}", decoded),
          Err(_) => format!("(could not decode) {:?}", &output),
        };
        e.command_with_context(
          command,
          format!("when analyzing exit status for output {}", output_msg),
        )
      })?;

      Ok(output)
    }

    pub fn decode(
      self,
      command: exe::Command,
    ) -> Result<DecodedOutput, exe::CommandErrorWrapper> {
      let Self { stdout, stderr } = &self;
      let stdout = str::from_utf8(stdout)
        .map_err(|e| e.into())
        .map_err(|e: exe::CommandError| {
          e.command_with_context(
            command.clone(),
            format!("when decoding stdout from {:?}", &self),
          )
        })?
        .to_string();
      let stderr = str::from_utf8(stderr)
        .map_err(|e| e.into())
        .map_err(|e: exe::CommandError| {
          e.command_with_context(command, format!("when decoding stderr from {:?}", &self))
        })?
        .to_string();
      Ok(DecodedOutput { stdout, stderr })
    }
  }

  #[derive(Debug, Clone)]
  pub struct DecodedOutput {
    pub stdout: String,
    pub stderr: String,
  }

  #[async_trait]
  pub trait SyncInvocable {
    /// Invoke a child process and wait on it to complete while slurping its output.
    async fn invoke(self) -> Result<RawOutput, exe::CommandErrorWrapper>;
  }

  #[async_trait]
  impl SyncInvocable for exe::Command {
    async fn invoke(self) -> Result<RawOutput, exe::CommandErrorWrapper> {
      let mut command = self.clone().command();
      let output =
        command
          .output()
          .await
          .map_err(|e| e.into())
          .map_err(|e: exe::CommandError| {
            e.command_with_context(self.clone(), format!("waiting for output"))
          })?;
      let output = RawOutput::extract(self, output)?;
      Ok(output)
    }
  }
}

pub mod stream {
  use super::exe;

  use async_process::{self, Child, ChildStderr, ChildStdout, Stdio};
  use futures_lite::{future, io::BufReader, prelude::*};

  use std::{future::Future, io, str};

  /// A handle to the result of [`SpackInvocation::invoke_streaming`].
  pub struct Streaming {
    /// The handle to the live child process (live until [`Child::output`] is called).
    pub child: Child,
    /// The stdout stream, separated from the process handle.
    pub stdout: ChildStdout,
    /// The stderr stream, separated from the process handler.
    pub stderr: ChildStderr,
    /// The command being executed.
    pub command: exe::Command,
  }

  impl Streaming {
    pub(crate) async fn exhaust_output_streams_and_wait<F>(
      self,
      act: fn(StdioLine) -> F,
    ) -> Result<(), exe::CommandErrorWrapper>
    where
      F: Future<Output = Result<(), exe::CommandError>>,
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
          StdioLine::merge_streams(out_lines.next().boxed(), err_lines.next().boxed()).await?
        {
          act(line).await?;
        }
        let output = child.status().await?;
        Ok(output)
      }
      .await
      .map_err(|e: exe::CommandError| {
        e.command_with_context(command.clone(), format!("merging async streams"))
      })?;

      exe::CommandError::analyze_exit_status(status)
        .map_err(|e| e.command_with_context(command, format!("checking async exit status")))?;
      Ok(())
    }

    /// Copy over all stderr lines to our stderr, and stdout lines to our stdout.
    async fn stdio_streams_callback(line: StdioLine) -> Result<(), exe::CommandError> {
      match line {
        StdioLine::Err(err) => {
          let err = str::from_utf8(err.as_bytes()).expect("UTF8 DECODING STDERR FAILED");
          eprintln!("{}", err);
        }
        StdioLine::Out(out) => {
          let out = str::from_utf8(out.as_bytes()).expect("UTF8 DECODING STDOUT FAILED");
          println!("{}", out);
        }
      }
      Ok(())
    }

    pub async fn wait(self) -> Result<(), exe::CommandErrorWrapper> {
      self
        .exhaust_output_streams_and_wait(Self::stdio_streams_callback)
        .await?;
      Ok(())
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

  pub trait Streamable {
    /// Invoke a child process and return a handle to its output streams.
    fn invoke_streaming(self) -> Result<Streaming, exe::CommandErrorWrapper>;
  }

  impl Streamable for exe::Command {
    fn invoke_streaming(self) -> Result<Streaming, exe::CommandErrorWrapper> {
      let mut command = self.clone().command();
      let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.into())
        .map_err(|e: exe::CommandError| {
          e.command_with_context(self.clone(), format!("spawning async process"))
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

pub mod python {
  use super::{
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
    static ref PYTHON_VERSION_REGEX: Regex = Regex::new(r"^Python (3\.[0-9]+\.[0-9]+)\n$").unwrap();
  }

  impl FoundPython {
    fn determine_python_exename() -> exe::Exe {
      let exe_name: OsString = env::var_os("SPACK_PYTHON").unwrap_or_else(|| "python3".into());
      let exe_path = Path::new(&exe_name).to_path_buf();
      exe::Exe(fs::File(exe_path))
    }

    /// Check for a valid python installation by parsing the output of `--version`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// # #[allow(unused_variables)]
    /// let python = spack::subprocess::python::FoundPython::detect().await.unwrap();
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
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
}

pub mod spack {
  use super::{
    base::{self, CommandBase},
    exe, fs, python,
    sync::SyncInvocable,
  };
  use crate::summoning;

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
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{subprocess::{python::*, spack::*}, summoning::*};
    ///
    /// // Access a few of the relevant files and directories.
    /// let python = FoundPython::detect().await.unwrap();
    /// let cache_dir = CacheDir::get_or_create().unwrap();
    /// let spack_exe = SpackRepo::summon(cache_dir).await.unwrap();
    /// let spack = SpackInvocation::create(python, spack_exe).await?;
    ///
    /// // This is the current version number for the spack installation.
    /// assert!(spack.version == "0.18.0.dev0".to_string());
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
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
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::subprocess::spack::SpackInvocation;
    ///
    /// let spack = SpackInvocation::summon().await?;
    /// // This is the current version number for the spack installation.
    /// assert!(spack.version == "0.18.0.dev0".to_string());
    /// # Ok(())
    /// # }) // async
    /// # }
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

pub mod sh {
  use super::{
    base::{self, CommandBase},
    exe, fs,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use displaydoc::Display;
  use indexmap::IndexMap;
  use tempfile::{NamedTempFile, TempPath};
  use thiserror::Error;

  use std::{
    ffi::OsString,
    io::{self, BufRead, Write},
    str,
  };

  #[derive(Debug, Display, Error)]
  pub enum ShellError {
    /// setup error {0}
    Setup(#[from] base::SetupErrorWrapper),
    /// command error {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// i/o error {0}
    Io(#[from] io::Error),
    /// utf-8 decoding error {0}
    Utf8(#[from] str::Utf8Error),
  }

  impl ShellError {
    pub fn with_context(self, context: String) -> ShellErrorWrapper {
      ShellErrorWrapper {
        context,
        error: self,
      }
    }
  }

  /// shell error ({context}): {error}
  #[derive(Debug, Display, Error)]
  pub struct ShellErrorWrapper {
    pub context: String,
    #[source]
    pub error: ShellError,
  }

  /// Generate a shell script to execute via [`ShellScript`].
  ///
  /// This script is generated by writing [`Self::contents`] to a temporary file.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use spack::{subprocess::{sh, exe, base::CommandBase, sync::SyncInvocable}};
  ///
  /// let contents = "echo hey".as_bytes().to_vec();
  /// let source = sh::ShellSource { contents };
  /// let script = source.into_script().await.expect("generating shell script failed");
  /// let command = script.with_command(exe::Command::default())
  ///   .setup_command().await.unwrap();
  ///
  /// let output = command.invoke().await.expect("shell script should succeed");
  /// assert!(b"hey\n".as_ref() == &output.stdout);
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  #[derive(Debug, Clone)]
  pub struct ShellSource {
    pub contents: Vec<u8>,
  }

  /* let runner_script_contents = format!("{}\n\nexec $@\n", load_env.0,); */
  impl ShellSource {
    fn write_to_temp_path(self) -> io::Result<TempPath> {
      /* Create the script. */
      let (mut script_file, script_path) = NamedTempFile::new()?.into_parts();
      let Self { contents } = self;
      script_file.write_all(&contents)?;
      script_file.sync_all()?;
      /* Close the file, but keep the path alive. */
      Ok(script_path)
    }

    pub async fn into_script(self) -> Result<ShellScript, ShellError> {
      let script_path = self.write_to_temp_path()?;

      /* FIXME: We don't ever delete the script! */
      let script_path = exe::Exe(fs::File(
        script_path
          .keep()
          .expect("should never be any error keeping the shell script path"),
      ));

      Ok(ShellScript { script_path })
    }
  }

  /// Request for dumping the components of the environment after evaluating a shell script.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use std::ffi::OsStr;
  /// use spack::subprocess::{sh, exe};
  ///
  /// let env = sh::EnvAfterScript {
  ///   source: sh::ShellSource {
  ///     contents: b"export A=3".to_vec(),
  ///   },
  /// };
  /// let exe::EnvModifications(env) = env.extract_env_bindings().await.unwrap();
  /// let env_val = env.get(OsStr::new("A")).unwrap().to_str().unwrap();
  /// assert_eq!(3, env_val.parse::<usize>().unwrap());
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  #[derive(Debug, Clone)]
  pub struct EnvAfterScript {
    pub source: ShellSource,
  }

  impl EnvAfterScript {
    fn into_source(self) -> ShellSource {
      let Self {
        source: ShellSource { mut contents },
      } = self;
      contents.extend_from_slice(b"\n\nexec env");
      ShellSource { contents }
    }

    async fn into_command(self) -> Result<exe::Command, ShellErrorWrapper> {
      /* Write script file. */
      let source = self.into_source();
      let script = source
        .into_script()
        .await
        .map_err(|e| e.with_context(format!("when writing env script to file")))?;
      /* Generate command. */
      let sh = script.with_command(exe::Command::default());
      let command = sh
        .setup_command()
        .await
        .map_err(|e| {
          e.with_context(format!("when setting up the shell command"))
            .into()
        })
        .map_err(|e: ShellError| {
          e.with_context(format!("when setting up the shell command, again"))
        })?;
      Ok(command)
    }

    async fn extract_stdout(self) -> Result<Vec<u8>, ShellErrorWrapper> {
      /* Setup command. */
      let command = self.into_command().await?;

      /* Execute command. */
      let output = command
        .invoke()
        .await
        .map_err(|e| e.into())
        .map_err(|e: ShellError| e.with_context(format!("when extracting env bindings")))?;

      Ok(output.stdout.clone())
    }

    pub async fn extract_env_bindings(self) -> Result<exe::EnvModifications, ShellErrorWrapper> {
      let stdout = self.extract_stdout().await?;

      /* Parse output into key-value pairs. */
      let mut env_map: IndexMap<OsString, OsString> = IndexMap::new();
      for line in stdout.lines() {
        let line = line
          .map_err(|e| e.into())
          .map_err(|e: ShellError| e.with_context(format!("when extracting stdout line")))?;
        /* FIXME: we currently just ignore lines that don't have an '=' -- fix this! */
        if let Some(equals_index) = line.find('=') {
          let key = &line[..equals_index];
          let value = &line[equals_index + 1..];
          env_map.insert(key.into(), value.into());
        }
      }

      Ok(exe::EnvModifications(env_map))
    }
  }

  /// Execute a command line beginning with this shell script.
  ///
  /// The later arguments provided via [`Self::with_command`] (FIXME!)
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use std::io::Write;
  /// use tempfile::NamedTempFile;
  /// use spack::subprocess::{sh, exe, sync::SyncInvocable, base::CommandBase, fs};
  ///
  /// let script_path = {
  ///   let (mut script_file, script_path) = NamedTempFile::new().unwrap().into_parts();
  ///   script_file.write_all(b"echo hey\n").unwrap();
  ///   script_file.sync_all().unwrap();
  ///   script_path.keep().unwrap()
  /// };
  /// let script_path = exe::Exe(fs::File(script_path));
  /// let script = sh::ShellScript { script_path };
  /// let command = script.with_command(exe::Command::default())
  ///   .setup_command().await.unwrap();
  ///
  /// let output = command.invoke().await.expect("script should succeed");
  /// assert!(b"hey\n".as_ref() == &output.stdout);
  /// # Ok(())
  /// # }) // async
  /// # }
  ///```
  #[derive(Debug, Clone)]
  pub struct ShellScript {
    pub script_path: exe::Exe,
  }

  impl ShellScript {
    pub fn with_command(self, base: exe::Command) -> ShellScriptInvocation {
      ShellScriptInvocation { script: self, base }
    }
  }

  #[derive(Debug, Clone)]
  pub struct ShellScriptInvocation {
    pub script: ShellScript,
    pub base: exe::Command,
  }

  #[async_trait]
  impl CommandBase for ShellScriptInvocation {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self {
        script: ShellScript { script_path },
        mut base,
      } = self;
      base.unshift_shell_script(script_path);
      Ok(base)
    }
  }
}
