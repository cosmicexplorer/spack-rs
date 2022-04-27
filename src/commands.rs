/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking specific spack commands.

use crate::invocation::{Argv, Invocation, InvocationError, StdioLine, Streaming};

use displaydoc::Display;

use serde::{Deserialize, Serialize};
use serde_json;
use thiserror::Error;

use std::{
  io::{self, BufRead, Write},
  path::PathBuf,
  process,
};

/// An (abstract *or* concrete) spec string for a command-line argument.
///
/// This is used in [`find::Find::find`] to resolve concrete specs from the string.
#[derive(Debug, Clone)]
pub struct CLISpec(pub String);

impl CLISpec {
  /// Construct a cli spec from a [str].
  pub fn new<R: AsRef<str>>(r: R) -> Self {
    Self(r.as_ref().to_string())
  }
}

/// Errors executing spack commands.
#[derive(Debug, Display, Error)]
pub enum CommandError {
  /// install error from {0:?}: {1}
  Install(install::Install, #[source] install::InstallError),
  /// find error from {0:?}: {1}
  Find(find::Find, #[source] find::FindError),
  /// build-env error from {0:?}: {1}
  BuildEnv(build_env::BuildEnv, #[source] build_env::BuildEnvError),
  /// python error from {0:?}: {1}
  Python(python::SpackPython, #[source] python::SpackPythonError),
  /// compiler-find error from {0:?}: {1}
  CompilerFind(
    compiler_find::CompilerFind,
    #[source] compiler_find::CompilerFindError,
  ),
}

/// Install command.
pub mod install {
  use super::{find::*, *};

  /// Errors installing.
  #[derive(Debug, Display, Error)]
  pub enum InstallError {
    /// {0}
    Inner(#[source] Box<crate::Error>),
    /// find error: {0}
    Find(#[from] FindError),
  }

  /// Install request.
  #[allow(missing_docs)]
  #[derive(Debug, Clone)]
  pub struct Install {
    pub spack: Invocation,
    pub spec: CLISpec,
  }

  impl Install {
    /// Execute `spack install "$self.spec"`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, install::*}, invocation::*, summoning::*};
    ///
    /// // Locate all the executables.
    /// let python = Python::detect().await?;
    /// let cache_dir = CacheDir::get_or_create()?;
    /// let spack_exe = SpackRepo::summon(cache_dir).await?;
    /// let spack = Invocation::create(python, spack_exe).await?;
    ///
    /// // Install libiberty, if we don't have it already!
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("libiberty@2.37") };
    /// let found_spec = install.clone().install().await
    ///   .map_err(|e| CommandError::Install(install, e))?;
    ///
    /// // The result matches our query!
    /// assert!(&found_spec.name == "libiberty");
    /// assert!(&found_spec.version.0 == "2.37");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn install(self) -> Result<FoundSpec, InstallError> {
      let Self { spack, spec } = self.clone();
      /* Generate spack argv. */
      let argv = Argv(
        [
          "install",
          "--verbose",
          "--fail-fast",
          /* FIXME: determine appropriate amount of build parallelism! */
          "-j16",
        ]
        .into_iter()
        .map(|s| s.to_string())
        .chain([spec.0.clone()].into_iter())
        .collect(),
      );

      /* Kick off the child process, reading its streams asynchronously. */
      let streaming = spack
        .clone()
        .invoke_streaming(argv.clone())
        .map_err(|e| InstallError::Inner(Box::new(crate::Error::Invocation(e))))?;
      streaming
        /* Copy over all stderr lines to our stderr, and stdout lines to our stdout. */
        .exhaust_output_streams_and_wait::<InvocationError, _>(async move |line| match line {
          StdioLine::Err(err) => {
            eprintln!("{}", err);
            Ok(())
          }
          StdioLine::Out(out) => {
            println!("{}", out);
            Ok(())
          }
        })
        .await
        .map_err(|e| InstallError::Inner(Box::new(crate::Error::Invocation(e))))?;

      /* Find the first match for the spec we just tried to install. */
      /* NB: this will probably immediately break if the CLI spec covers more than one concrete
       * spec! For now we just take the first result!! */
      let find = Find { spack, spec };
      let found_specs = find
        .clone()
        .find()
        .await
        .map_err(|e| CommandError::Find(find, e))
        .map_err(|e| InstallError::Inner(Box::new(crate::Error::from(e))))?;
      Ok(found_specs[0].clone())
    }
  }
}

/// A concrete version string from [find::FoundSpec::version].
#[derive(Debug, Display, Serialize, Deserialize, Clone)]
pub struct ConcreteVersion(pub String);

/// Find command.
pub mod find {
  use super::*;

  /// A single package's spec from running [`Find::find`].
  #[derive(Debug, Display, Serialize, Deserialize, Clone)]
  pub struct FoundSpec {
    /// package name: {0}
    pub name: String,
    /// concrete package version: {0}
    pub version: ConcreteVersion,
    arch: serde_json::Value,
    compiler: serde_json::Value,
    namespace: String,
    parameters: serde_json::Value,
    dependencies: Option<serde_json::Value>,
    /// 32-character hash uniquely identifying this spec: {0}
    pub hash: String,
    full_hash: String,
  }

  impl FoundSpec {
    /// Get a CLI argument matching the exact spec found previously.
    pub fn hashed_spec(&self) -> CLISpec {
      CLISpec(format!("{}/{}", &self.name, &self.hash))
    }
  }

  /// Errors finding.
  #[derive(Debug, Display, Error)]
  pub enum FindError {
    /// {0}
    Inner(#[source] Box<crate::Error>),
    /// json error {0}: {1}
    Serde(String, #[source] serde_json::Error),
    /// unknown error: {0}
    Unknown(String),
  }

  /// Find request.
  #[allow(missing_docs)]
  #[derive(Debug, Clone)]
  pub struct Find {
    pub spack: Invocation,
    pub spec: CLISpec,
  }

  impl Find {
    /// Execute `spack find "$self.spec"`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, install::*, find::*}, invocation::*, summoning::*};
    ///
    /// // Locate our scripts.
    /// let python = Python::detect().await?;
    /// let cache_dir = CacheDir::get_or_create()?;
    /// let spack_exe = SpackRepo::summon(cache_dir).await?;
    /// let spack = Invocation::create(python, spack_exe).await?;
    ///
    /// // Ensure a python is installed that is at least version 3.
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("python@3:") };
    /// let found_spec = install.clone().install().await
    ///   .map_err(|e| CommandError::Install(install, e))?;
    ///
    /// // Look for a python spec with that exact hash.
    /// let find = Find { spack, spec: found_spec.hashed_spec() };
    ///
    /// // .find() will return an array of values, which may have any length.
    /// let found_specs = find.clone().find().await
    ///   .map_err(|e| CommandError::Find(find, e))?;
    ///
    /// // We just choose the first.
    /// assert!(&found_specs[0].name == "python");
    /// // Verify that this is the same spec as before.
    /// assert!(&found_specs[0].hash == &found_spec.hash);
    /// // The fields of the '--json' output of 'find'
    /// // are deserialized into FoundSpec instances.
    /// assert!(&found_specs[0].version.0[..2] == "3.");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn find(self) -> Result<Vec<FoundSpec>, FindError> {
      let Self { spack, spec } = self.clone();
      let args = Argv(
        ["find", "--json"]
          .into_iter()
          .map(|s| s.to_string())
          .chain([spec.0].into_iter())
          .collect(),
      );
      let process::Output { stdout, .. } = spack
        .clone()
        .invoke(args.clone())
        .await
        .map_err(|e| FindError::Inner(Box::new(crate::Error::Invocation(e))))?;
      match serde_json::from_slice::<'_, serde_json::Value>(&stdout)
        .map_err(|e| FindError::Serde(format!("{:?}", &stdout), e))?
      {
        serde_json::Value::Array(values) => {
          let found_specs: Vec<FoundSpec> = values
            .into_iter()
            .map(|v| serde_json::from_value(v))
            .collect::<Result<Vec<FoundSpec>, _>>()
            .map_err(|e| FindError::Serde(format!("{:?}", &stdout), e))?;
          Ok(found_specs)
        }
        value => Err(FindError::Unknown(format!(
          "unable to parse find output: {:?}",
          value
        ))),
      }
    }
  }
}

/// Build-env command.
pub mod build_env {
  use super::*;

  /// Errors setting up the build environment.
  #[derive(Debug, Display, Error)]
  pub enum BuildEnvError {
    /// {0}
    Inner(#[source] Box<crate::Error>),
    /// io error: {0}
    Io(#[from] io::Error),
  }

  /// Build-env request.
  #[derive(Debug, Clone)]
  pub struct BuildEnv {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// Which spec to get into the environment of.
    pub spec: CLISpec,
    /// Optional output file for sourcing environment modifications.
    pub dump: Option<PathBuf>,
    /// Optional command line to evaluate within the package environment.
    ///
    /// If this argv is empty, the contents of the environment are printed to stdout with `env`.
    pub argv: Argv,
  }

  impl BuildEnv {
    fn dump_args(&self) -> io::Result<Vec<String>> {
      dbg!(self);
      let args = if let Some(d) = &self.dump {
        vec!["--dump".to_string(), format!("{}", d.display())]
      } else {
        vec![]
      };
      Ok(args)
    }

    /// Execute `spack build-env "$self.spec" -- $self.argv`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// let td = tempdir::TempDir::new("spack-summon-test")?;
    /// use std::{fs, io::BufRead, process::Output};
    /// use spack::{commands::{*, build_env::*, install::*}, invocation::*, summoning::*};
    ///
    /// // Locate all the executables.
    /// let python = Python::detect().await?;
    /// let cache_dir = CacheDir::get_or_create()?;
    /// let spack_exe = SpackRepo::summon(cache_dir).await?;
    /// let spack = Invocation::create(python, spack_exe).await?;
    ///
    /// // Let's get a python 3 or later installed!
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("python@3:") };
    /// let found_spec = install.clone().install().await
    ///   .map_err(|e| CommandError::Install(install, e))?;
    ///
    /// // Now let's activate the build environment for it!
    /// let build_env = BuildEnv {
    ///   spack: spack.clone(),
    ///   // Use the precise spec we just ensured was installed.
    ///   spec: found_spec.hashed_spec(),
    ///   dump: None,
    ///   argv: Argv(vec![]),
    /// };
    /// // Execute build-env to get an env printed to stdout.
    /// let output = build_env.clone().build_env().await
    ///   .map_err(|e| CommandError::BuildEnv(build_env, e))?;
    ///
    /// // Example ad-hoc parsing of environment source files.
    /// let mut spec_was_found: bool = false;
    /// for line in output.stdout.lines() {
    ///   let line = line?;
    ///   if line.starts_with("SPACK_SHORT_SPEC") {
    ///     spec_was_found = true;
    ///     assert!("python" == &line[17..23]);
    ///   }
    /// }
    /// assert!(spec_was_found);
    ///
    /// // Now let's write out the environment to a file using --dump!
    /// let dump = td.path().join(".env-dump");
    /// let build_env = BuildEnv {
    ///   spack: spack.clone(),
    ///   spec: found_spec.hashed_spec(),
    ///   dump: Some(dump.clone()),
    ///   argv: Argv(vec![]),
    /// };
    /// // We will have written to ./.env-dump!
    /// let _ = build_env.clone().build_env().await
    ///   .map_err(|e| CommandError::BuildEnv(build_env, e))?;
    /// spec_was_found = false;
    /// for line in fs::read_to_string(&dump)?.lines() {
    ///   if line.starts_with("SPACK_SHORT_SPEC") {
    ///     spec_was_found = true;
    ///     assert!("python" == &line[18..24]);
    ///   }
    /// }
    /// assert!(spec_was_found);
    ///
    /// // Now let's try running a command line in a build-env!
    /// let build_env = BuildEnv {
    ///   spack,
    ///   spec: found_spec.hashed_spec(),
    ///   dump: None,
    ///   argv: ["sh", "-c", "echo $SPACK_SHORT_SPEC"].as_ref().into(),
    /// };
    /// let Output { stdout, .. } = build_env.clone().build_env().await
    ///   .map_err(|e| CommandError::BuildEnv(build_env, e))?;
    /// assert!(&stdout[..6] == b"python");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn build_env(self) -> Result<process::Output, BuildEnvError> {
      let argv = Argv(
        ["build-env".to_string()]
          .into_iter()
          .chain(self.dump_args()?.into_iter())
          .chain([self.spec.0.to_string()].into_iter())
          .chain(self.argv.trailing_args().0.into_iter())
          .collect(),
      );
      let output = self
        .spack
        .invoke(argv)
        .await
        .map_err(|e| BuildEnvError::Inner(Box::new(crate::Error::Invocation(e))))?;
      Ok(output)
    }
  }
}

/// spack python command.
pub mod python {
  use super::*;

  use tempfile::{NamedTempFile, TempPath};

  use std::path::Path;

  /// Errors executing spack's python interpreter.
  #[derive(Debug, Display, Error)]
  pub enum SpackPythonError {
    /// {0}
    Inner(#[source] Box<crate::Error>),
    /// io error {0}
    Io(#[from] io::Error),
  }

  /// spack python command request.
  #[derive(Debug, Clone)]
  pub struct SpackPython {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// The contents of the python script to execute.
    pub script: String,
    /// Further command-line args to pass to the python script.
    pub argv: Argv,
  }

  impl SpackPython {
    fn setup_command(script: String, argv: Argv) -> io::Result<(TempPath, Argv)> {
      /* Create the script. */
      let script_path = {
        let (mut script_file, script_path) = NamedTempFile::new()?.into_parts();
        script_file.write_all(script.as_bytes())?;
        script_file.sync_all()?;
        script_path
      };

      /* Craft the command line. */
      let script_path_ref: &Path = script_path.as_ref();
      let argv = Argv(
        [
          "python".to_string(),
          format!("{}", script_path_ref.display()),
        ]
        .into_iter()
        .chain(argv.as_strs().into_iter().map(|s| s.to_string()))
        .collect(),
      );

      Ok((script_path, argv))
    }

    /// Execute `spack python <$self.script $self.argv`.
    ///
    /// See [`Invocation::invoke`].
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use std::{process::Output, str};
    /// use spack::{commands::{*, python::*}, invocation::*, summoning::*};
    ///
    /// // Locate executable scripts.
    /// let python = Python::detect().await?;
    /// let cache_dir = CacheDir::get_or_create()?;
    /// let spack_exe = SpackRepo::summon(cache_dir).await?;
    /// let spack = Invocation::create(python, spack_exe).await?;
    ///
    /// // Create python execution request.
    /// let spack_python = SpackPython {
    ///   spack: spack.clone(),
    ///   script: "import spack; print(spack.__version__)".to_string(),
    ///   argv: Argv(vec![]),
    /// };
    ///
    /// // Spawn the child process and wait for it to end.
    /// let Output { stdout, .. } = spack_python.clone().invoke().await
    ///   .map_err(|e| CommandError::Python(spack_python, e))?;
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
    pub async fn invoke(self) -> Result<process::Output, SpackPythonError> {
      let Self {
        spack,
        script,
        argv,
      } = self;

      let (_script_path, argv) = Self::setup_command(script, argv)?;
      let output = spack
        .invoke(argv)
        .await
        .map_err(|e| SpackPythonError::Inner(Box::new(crate::Error::Invocation(e))))?;
      Ok(output)
    }

    /// Execute `spack python <$self.script $self.argv` and stream its output.
    ///
    /// See [`Invocation::invoke_streaming`].
    ///```
    /// #[allow(warnings)]
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use futures_lite::prelude::*;
    /// use spack::{commands::{*, python::*}, invocation::*, summoning::*};
    ///
    /// // Locate executable scripts.
    /// let python = Python::detect().await?;
    /// let cache_dir = CacheDir::get_or_create()?;
    /// let spack_exe = SpackRepo::summon(cache_dir).await?;
    /// let spack = Invocation::create(python, spack_exe).await?;
    ///
    /// // Create python execution request.
    /// let spack_python = SpackPython {
    ///   spack: spack.clone(),
    ///   script: "import spack; print(spack.__version__)".to_string(),
    ///   argv: Argv(vec![]),
    /// };
    ///
    /// // Spawn the child process and wait for it to end.
    /// let Streaming { child, mut stdout, .. } = spack_python.clone().invoke_streaming()
    ///   .map_err(|e| CommandError::Python(spack_python, e))?;
    ///
    /// // Slurp stdout all at once into a string.
    /// let mut version: String = "".to_string();
    /// stdout.read_to_string(&mut version).await?;
    /// // Parse the spack version from stdout, and verify it matches `spack.version`.
    /// let version = version.strip_suffix("\n").unwrap();
    /// assert!(version == &spack.version);
    ///
    /// // Now verify the process exited successfully.
    /// let output = child.output().await?;
    /// spack.analyze_exit_status(Argv(vec![]), output)?;
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub fn invoke_streaming(self) -> Result<Streaming, SpackPythonError> {
      let Self {
        spack,
        script,
        argv,
      } = self;

      let (script_path, argv) = Self::setup_command(script, argv)?;
      /* FIXME: We don't ever delete the script! */
      script_path.keep().unwrap();
      let streaming = spack
        .invoke_streaming(argv)
        .map_err(|e| SpackPythonError::Inner(Box::new(crate::Error::Invocation(e))))?;
      Ok(streaming)
    }
  }
}

/// Compiler-find command.
pub mod compiler_find {
  use super::*;

  /// Errors locating a compiler.
  #[derive(Debug, Display, Error)]
  pub enum CompilerFindError {
    /// {0}
    Inner(#[source] Box<crate::Error>),
    /// io error {0}
    Io(#[from] io::Error),
  }

  /// Compiler-find request.
  #[derive(Debug, Clone)]
  pub struct CompilerFind {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// Paths to search for compilers in.
    pub paths: Vec<PathBuf>,
  }

  /// A compiler found by [CompilerFind::compiler_find].
  pub struct FoundCompiler {
    /// The compiler spec for the found compiler.
    pub spec: String,
  }

  const COMPILER_SPEC_SOURCE: &str = include_str!("compiler-find.py");

  impl CompilerFind {
    /// Run `spack compiler find $self.paths`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, compiler_find::*}, invocation::*, summoning::*};
    ///
    /// // Locate all the executables.
    /// let python = Python::detect().await?;
    /// let cache_dir = CacheDir::get_or_create()?;
    /// let spack_exe = SpackRepo::summon(cache_dir).await?;
    /// let spack = Invocation::create(python, spack_exe).await?;
    ///
    /// // Create compiler-find execution request.
    /// let compiler_find = CompilerFind {
    ///   spack: spack.clone(),
    ///   paths: vec![],
    /// };
    /// let found_compilers = compiler_find.clone().compiler_find().await
    ///   .map_err(|e| CommandError::CompilerFind(compiler_find, e))?;
    /// // The first compiler on the list is clang!
    /// assert!(found_compilers[0].spec.starts_with("clang"));
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn compiler_find(self) -> Result<Vec<FoundCompiler>, CompilerFindError> {
      let Self { spack, paths } = self.clone();

      let python = python::SpackPython {
        spack: spack.clone(),
        script: COMPILER_SPEC_SOURCE.to_string(),
        argv: Argv(
          paths
            .into_iter()
            .map(|p| format!("{}", p.display()))
            .collect(),
        ),
      };
      let output = python
        .clone()
        .invoke()
        .await
        .map_err(|e| CommandError::Python(python, e))
        .map_err(|e| CompilerFindError::Inner(Box::new(e.into())))?;

      let mut compilers = Vec::new();
      for line in output.stdout.lines() {
        compilers.push(FoundCompiler {
          spec: line?.to_string(),
        });
      }
      Ok(compilers)
    }
  }
}
