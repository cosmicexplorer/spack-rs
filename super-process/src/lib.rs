/*
 * Description: An async process creation framework. More of a utility
 * library.
 *
 * Copyright (C) 2022 Danny McClanahan <dmcC2@hypnicjerk.ai>
 * SPDX-License-Identifier: Apache-2.0
 */

//! An async process creation framework. More of a utility library.
//!
//! - *TODO: [`fs`] doesn't do much yet.*
//! - [`exe::Command`] covers all the configuration for a single process
//!   invocation.
//! - [`base::CommandBase`] abstracts a process invocation which requires setup
//!   work.
//! - [`sync`] and [`stream`] invoke processes "synchronously" or
//!   "asynchronously".
//! - [`sh`] wraps a shell script invocation.

#![deny(rustdoc::missing_crate_level_docs)]
#![warn(missing_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
#![deny(clippy::all)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::result_large_err)]

/// Representations of filesystem locations on the local host.
///
/// *TODO: currently these don't do any validation!*
pub mod fs {
  use displaydoc::Display;

  use std::path::PathBuf;

  /// Trait for objects representing a handle to a filesystem path.
  pub(crate) trait PathWrapper {
    /// Consume this object and return a path.
    fn into_path_buf(self) -> PathBuf;
  }

  /// @={0}
  ///
  /// A path to a file that is assumed to already exist.
  #[derive(Debug, Display, Clone)]
  #[ignore_extra_doc_attributes]
  pub struct File(pub PathBuf);

  impl PathWrapper for File {
    fn into_path_buf(self) -> PathBuf {
      let Self(path) = self;
      path
    }
  }

  /// @<{0}
  ///
  /// A path to a directory that is assumed to already exist.
  #[derive(Debug, Display, Clone)]
  #[ignore_extra_doc_attributes]
  pub struct Directory(pub PathBuf);

  impl PathWrapper for Directory {
    fn into_path_buf(self) -> PathBuf {
      let Self(path) = self;
      path
    }
  }
}

/// Representations of executable files and methods to invoke them as async
/// processes.
pub mod exe {
  use super::fs::{self, PathWrapper};

  use displaydoc::Display;
  use indexmap::IndexMap;
  use lazy_static::lazy_static;
  use signal_hook::consts::{signal::*, TERM_SIGNALS};
  use thiserror::Error;

  use std::{
    collections::VecDeque,
    ffi::{OsStr, OsString},
    io, iter,
    os::unix::process::ExitStatusExt,
    path::{Path, PathBuf},
    process, str,
  };

  /// *{0}
  ///
  /// A path to an executable file which is assumed to exist.
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
    fn default() -> Self { Self(fs::File(PathBuf::default())) }
  }

  impl Exe {
    /// This is the default state of the executable.
    ///
    /// If an executable in this state is invoked, a panic will occur.
    pub fn is_empty(&self) -> bool {
      let Self(fs::File(exe)) = self;
      exe.as_os_str().is_empty()
    }
  }

  impl PathWrapper for Exe {
    fn into_path_buf(self) -> PathBuf {
      let Self(exe) = self;
      exe.into_path_buf()
    }
  }

  /// [{0:?}]
  ///
  /// The command line to provide to the executable. Note that the complete
  /// "argv" used by [`Command`] contains the executable path prefixed to
  /// these arguments.
  #[derive(Debug, Display, Clone, Default)]
  #[ignore_extra_doc_attributes]
  pub struct Argv(pub VecDeque<OsString>);

  impl<R: AsRef<OsStr>, I: iter::IntoIterator<Item=R>> From<I> for Argv {
    fn from(value: I) -> Self {
      let argv: VecDeque<OsString> = value
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
    /// If we're non-empty, prefix ourself with `--`.
    pub fn trailing_args(mut self) -> Self {
      if self.0.is_empty() {
        Self(VecDeque::new())
      } else {
        self.unshift("--".into());
        self
      }
    }

    /// Prefix ourself with the given `leftmost_arg`.
    pub fn unshift(&mut self, leftmost_arg: OsString) {
      let Self(ref mut argv) = self;
      argv.push_front(leftmost_arg);
    }
  }

  /// [{0:?}]
  ///
  /// Environment variables to set in the subprocess environment.
  #[derive(Debug, Display, Clone, Default)]
  #[ignore_extra_doc_attributes]
  pub struct EnvModifications(pub IndexMap<OsString, OsString>);

  impl<R: AsRef<OsStr>, I: iter::IntoIterator<Item=(R, R)>> From<I> for EnvModifications {
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
  /// Request to execute a subprocess. See [`crate::sync`] and [`crate::stream`]
  /// for examples of invocation.
  #[derive(Debug, Display, Clone, Default)]
  #[ignore_extra_doc_attributes]
  pub struct Command {
    /// Executable name, which may be absolute or relative to `$PATH` entries.
    pub exe: Exe,
    /// The working directory for the child process; otherwise, the working
    /// directory is inherited from the parent process.
    pub wd: Option<fs::Directory>,
    /// Arguments to pass to the executable. These should *not* be quoted at
    /// all.
    pub argv: Argv,
    /// Any new environment variables to set within the child process. The
    /// environment is otherwise inherited from the parent.
    pub env: EnvModifications,
  }

  impl Command {
    pub(crate) fn command(self) -> async_process::Command {
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

    /// Make this command execute the `new_exe` binary instead, shifting all
    /// args one to the right.
    pub fn unshift_new_exe(&mut self, new_exe: Exe) {
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

    pub(crate) fn command_with_context(
      self,
      command: Command,
      context: String,
    ) -> CommandErrorWrapper {
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
    /// Additional information about where the error occurred.
    pub context: String,
    /// The underlying error.
    #[source]
    pub error: CommandError,
  }
}

/// Extend the concept of a "process" to include setup, to enable abstraction.
pub mod base {
  use super::*;

  use async_trait::async_trait;
  use displaydoc::Display;
  use thiserror::Error;

  use std::io;

  /// Errors which may occur during the execution of
  /// [`CommandBase::setup_command`].
  #[derive(Debug, Display, Error)]
  pub enum SetupError {
    /// inner error: {0}
    Inner(#[source] Box<SetupErrorWrapper>),
    /// i/o error: {0}
    Io(#[from] io::Error),
  }

  impl SetupError {
    /// Wrap a raw error with `context` to produced a wrapped error.
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
    /// Additional information about where the error occurred.
    pub context: String,
    /// The underlying error.
    #[source]
    pub error: SetupError,
  }

  /// Declare higher-level operations which desugar to command lines by
  /// implementing this trait.
  #[async_trait]
  pub trait CommandBase {
    /// Generate a command line from the given object.
    async fn setup_command(self) -> Result<exe::Command, SetupError>;
  }
}

/// Methods to execute a process "synchronously", i.e. waiting until it has
/// exited.
///
///```
/// # tokio_test::block_on(async {
/// use std::{str, path::PathBuf};
/// use super_process::{fs, exe, sync::SyncInvocable};
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
/// assert_eq!(hey, "hey");
/// # }) // async
/// ```
pub mod sync {
  use super::exe;

  use async_trait::async_trait;

  use std::{process, str};

  /// The slurped streams for a synchronously-invoked process, as raw bytes.
  #[derive(Debug, Clone)]
  #[allow(missing_docs)]
  pub struct RawOutput {
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
  }

  impl RawOutput {
    /// Parse the process's exit status with
    /// [`exe::CommandError::analyze_exit_status`].
    pub async fn extract(
      command: exe::Command,
      output: process::Output,
    ) -> Result<Self, exe::CommandErrorWrapper> {
      let process::Output {
        status,
        stdout,
        stderr,
      } = output;

      let output = Self { stdout, stderr };
      if let Err(e) = exe::CommandError::analyze_exit_status(status) {
        let output_msg: String = match output.clone().decode(command.clone()).await {
          Ok(decoded) => format!("(utf-8 decoded) {:?}", decoded),
          Err(_) => format!("(could not decode) {:?}", &output),
        };
        return Err(e.command_with_context(
          command,
          format!("when analyzing exit status for output {}", output_msg),
        ));
      }

      Ok(output)
    }

    /// Decode the output streams of this process, with the invoking `command`
    /// provided for error context.
    pub async fn decode(
      self,
      command: exe::Command,
    ) -> Result<DecodedOutput, exe::CommandErrorWrapper> {
      tokio::task::spawn_blocking(move || {
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
        Ok::<_, exe::CommandErrorWrapper>(DecodedOutput { stdout, stderr })
      })
      .await
      .unwrap()
    }
  }

  /// The slurped streams for a synchronously-invoked process, after UTF-8
  /// decoding.
  #[derive(Debug, Clone)]
  #[allow(missing_docs)]
  pub struct DecodedOutput {
    pub stdout: String,
    pub stderr: String,
  }

  /// Trait that defines "synchronously" invokable processes.
  #[async_trait]
  pub trait SyncInvocable {
    /// Invoke a child process and wait on it to complete while slurping its
    /// output.
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
            e.command_with_context(self.clone(), "waiting for output".to_string())
          })?;
      let output = RawOutput::extract(self, output).await?;
      Ok(output)
    }
  }
}

/// Methods to execute a process in an "asynchronous" or "streaming" fashion.
///
/// **TODO: define a generic stream type like the `Emission` trait in
/// `learning-progress-bar`, then express the stdio lines stream in terms of the
/// stdio byte chunks stream!** We avoid doing that here because we expect using
/// a [`BufReader`](futures_lite::io::BufReader) to produce
/// [`StdioLine`](stream::StdioLine)s will be more efficient and cleaner than
/// manually implementing a `BufReader` with `async-channel` or something.
///
///```
/// # tokio_test::block_on(async {
/// use std::path::PathBuf;
/// use futures_lite::io::AsyncReadExt;
/// use super_process::{fs, exe, stream::Streamable};
///
/// let command = exe::Command {
///   exe: exe::Exe(fs::File(PathBuf::from("echo"))),
///   argv: ["hey"].as_ref().into(),
///   ..Default::default()
/// };
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
/// # }) // async
/// ```
pub mod stream {
  use super::exe;

  use async_process::{self, Child, ChildStderr, ChildStdout, Stdio};
  use futures_lite::{io::BufReader, prelude::*};

  use std::{future::Future, str};

  /// A handle to the result an asynchronous invocation.
  pub struct Streaming {
    /// The handle to the live child process (live until [`Child::output`] is
    /// called).
    pub child: Child,
    /// The stdout stream, separated from the process handle.
    pub stdout: ChildStdout,
    /// The stderr stream, separated from the process handler.
    pub stderr: ChildStderr,
    /// The command being executed.
    pub command: exe::Command,
  }

  impl Streaming {
    /// Stream the output of this process through `act`, then analyze the exit
    /// status.
    pub async fn exhaust_byte_streams_and_wait<F, A>(
      self,
      act: A,
    ) -> Result<(), exe::CommandErrorWrapper>
    where
      F: Future<Output=Result<(), exe::CommandError>>,
      A: Fn(StdioChunk) -> F,
    {
      let Self {
        mut stdout,
        mut stderr,
        mut child,
        command,
      } = self;

      let status = async move {
        let mut out_buf = [0u8; 300];
        let mut err_buf = [0u8; 300];
        /* TODO: find a nicer way to handle this loop! */
        let mut out_done: bool = false;
        let mut err_done: bool = false;
        loop {
          if out_done {
            if err_done {
              break;
            } else {
              let num_read = stderr.read(&mut err_buf).await?;
              if num_read == 0 {
                err_done = true;
              } else {
                let chunk = StdioChunk::Err(err_buf[..num_read].to_vec());
                act(chunk).await?;
              }
            }
          } else {
            if err_done {
              let num_read = stdout.read(&mut out_buf).await?;
              if num_read == 0 {
                out_done = true;
              } else {
                let chunk = StdioChunk::Out(out_buf[..num_read].to_vec());
                act(chunk).await?;
              }
            } else {
              tokio::select! {
                Ok(num_read) = stdout.read(&mut out_buf) => {
                  if num_read == 0 {
                    out_done = true;
                  } else {
                    let chunk = StdioChunk::Out(out_buf[..num_read].to_vec());
                    act(chunk).await?;
                  }
                }
                Ok(num_read) = stderr.read(&mut err_buf) => {
                  if num_read == 0 {
                    err_done = true;
                  } else {
                    let chunk = StdioChunk::Err(err_buf[..num_read].to_vec());
                    act(chunk).await?;
                  }
                }
                else => { break; }
              }
            }
          }
        }
        let output = child.status().await?;
        Ok(output)
      }
      .await
      .map_err(|e: exe::CommandError| {
        e.command_with_context(command.clone(), "merging async streams".to_string())
      })?;

      exe::CommandError::analyze_exit_status(status)
        .map_err(|e| e.command_with_context(command, "checking async exit status".to_string()))?;
      Ok(())
    }

    /// Stream the output of this process through `act`, then analyze the exit
    /// status.
    pub async fn exhaust_string_streams_and_wait<F, A>(
      self,
      act: A,
    ) -> Result<(), exe::CommandErrorWrapper>
    where
      F: Future<Output=Result<(), exe::CommandError>>,
      A: Fn(StdioLine) -> F,
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
        loop {
          let line = tokio::select! {
            Some(err) = err_lines.next() => StdioLine::Err(err?),
            Some(out) = out_lines.next() => StdioLine::Out(out?),
            else => break,
          };
          act(line).await?;
        }
        let output = child.status().await?;
        Ok(output)
      }
      .await
      .map_err(|e: exe::CommandError| {
        e.command_with_context(command.clone(), "merging async streams".to_string())
      })?;

      exe::CommandError::analyze_exit_status(status)
        .map_err(|e| e.command_with_context(command, "checking async exit status".to_string()))?;
      Ok(())
    }

    /// Copy over all stderr lines to our stderr, and stdout lines to our
    /// stdout.
    async fn stdio_streams_callback(line: StdioLine) -> Result<(), exe::CommandError> {
      match line {
        StdioLine::Err(err) => {
          let err = str::from_utf8(err.as_bytes()).expect("UTF8 DECODING STDERR FAILED");
          eprintln!("{}", err);
        },
        StdioLine::Out(out) => {
          let out = str::from_utf8(out.as_bytes()).expect("UTF8 DECODING STDOUT FAILED");
          println!("{}", out);
        },
      }
      Ok(())
    }

    /// Wait for the process to exit, printing lines of stdout and stderr to the
    /// terminal.
    pub async fn wait(self) -> Result<(), exe::CommandErrorWrapper> {
      self
        .exhaust_string_streams_and_wait(Self::stdio_streams_callback)
        .await?;
      Ok(())
    }
  }

  /// A chunk of either stdout or stderr from a subprocess.
  #[derive(Debug, Clone, PartialEq, Eq)]
  pub enum StdioChunk {
    /// A chunk of stdout.
    Out(Vec<u8>),
    /// A chunk of stderr.
    Err(Vec<u8>),
  }

  /// A line of either stdout or stderr from a subprocess.
  #[derive(Debug, Clone, PartialEq, Eq)]
  pub enum StdioLine {
    /// A line of stdout.
    Out(String),
    /// A line of stderr.
    Err(String),
  }

  /// Trait that defines "asynchronously" invokable processes.
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
          e.command_with_context(self.clone(), "spawning async process".to_string())
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

/// Methods to execute a shell script as a process.
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

  /// Errors that may occur when executing a shell script.
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
    /// Wrap a raw error with `context` to produced a wrapped error.
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
    /// Additional information about where the error occurred.
    pub context: String,
    /// The underlying error.
    #[source]
    pub error: ShellError,
  }

  /// Generate a shell script to execute via [`ShellScript`].
  ///
  /// This script is generated by writing [`Self::contents`] to a temporary
  /// file. ```
  /// # tokio_test::block_on(async {
  /// use super_process::{sh, exe, base::CommandBase, sync::SyncInvocable};
  ///
  /// let contents = "echo hey".as_bytes().to_vec();
  /// let source = sh::ShellSource { contents };
  /// let script = source.into_script().await.expect("generating shell script
  /// failed"); let command = script.with_command(exe::Command::default())
  ///   .setup_command().await.unwrap();
  ///
  /// let output = command.invoke().await.expect("shell script should succeed");
  /// assert!(b"hey\n".as_ref() == &output.stdout);
  /// # }) // async
  /// ```
  #[derive(Debug, Clone)]
  pub struct ShellSource {
    /// The bytes of a shell script to be written to file.
    pub contents: Vec<u8>,
  }

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

    /// Create a handle to a shell script backed by a temp file.
    ///
    /// *FIXME: we don't ever delete the temp file! Use lifetimes to avoid
    /// this!*
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

  /// Request for dumping the components of the environment after evaluating a
  /// shell script. ```
  /// # tokio_test::block_on(async {
  /// use std::ffi::OsStr;
  /// use super_process::{sh, exe};
  ///
  /// let env = sh::EnvAfterScript {
  ///   source: sh::ShellSource {
  ///     contents: b"export A=3".to_vec(),
  ///   },
  /// };
  /// let exe::EnvModifications(env) =
  /// env.extract_env_bindings().await.unwrap(); let env_val =
  /// env.get(OsStr::new("A")).unwrap().to_str().unwrap(); assert_eq!(3,
  /// env_val.parse::<usize>().unwrap()); # }) // async
  /// ```
  #[derive(Debug, Clone)]
  pub struct EnvAfterScript {
    /// Script to run before extracting the environment.
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
        .map_err(|e| e.with_context("when writing env script to file".to_string()))?;
      /* Generate command. */
      let sh = script.with_command(exe::Command::default());
      let command = sh
        .setup_command()
        .await
        .map_err(|e| {
          e.with_context("when setting up the shell command".to_string())
            .into()
        })
        .map_err(|e: ShellError| {
          e.with_context("when setting up the shell command, again".to_string())
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
        .map_err(|e: ShellError| e.with_context("when extracting env bindings".to_string()))?;

      Ok(output.stdout)
    }

    /// Execute the wrapped script and parse the output of the `env` command
    /// executed afterwards!
    pub async fn extract_env_bindings(self) -> Result<exe::EnvModifications, ShellErrorWrapper> {
      let stdout = self.extract_stdout().await?;

      /* Parse output into key-value pairs. */
      let mut env_map: IndexMap<OsString, OsString> = IndexMap::new();
      for line in stdout.lines() {
        let line = line
          .map_err(|e| e.into())
          .map_err(|e: ShellError| e.with_context("when extracting stdout line".to_string()))?;
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
  /// # tokio_test::block_on(async {
  /// use std::io::Write;
  /// use tempfile::NamedTempFile;
  /// use super_process::{sh, exe, sync::SyncInvocable, base::CommandBase, fs};
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
  /// # }) // async
  /// ```
  #[derive(Debug, Clone)]
  pub struct ShellScript {
    /// The script to execute.
    pub script_path: exe::Exe,
  }

  impl ShellScript {
    /// Provide a command line for this shell script to execute.
    pub fn with_command(self, base: exe::Command) -> ShellScriptInvocation {
      ShellScriptInvocation { script: self, base }
    }
  }

  /// The command wrapper for a shell script.
  #[derive(Debug, Clone)]
  pub struct ShellScriptInvocation {
    /// The script to preface the command line with.
    pub script: ShellScript,
    /// The command line to provide to the script.
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
