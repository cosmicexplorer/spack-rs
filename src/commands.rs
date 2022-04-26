/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking specific spack commands.

use crate::invocation::{Argv, Invocation, InvocationError, StdioLine};

use displaydoc::Display;

use serde::{Deserialize, Serialize};
use serde_json;
use thiserror::Error;

use std::{io, path::PathBuf, process};

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
