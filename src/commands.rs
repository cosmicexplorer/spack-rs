/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking specific spack commands.

use displaydoc::Display;
use thiserror::Error;

use std::{
  io::{self, Write},
  path::PathBuf,
};

/// {0}
///
/// An (abstract *or* concrete) spec string for a command-line argument. This is used in
/// [`find::Find::find`] to resolve concrete specs from the string.
#[derive(Debug, Display, Clone)]
#[ignore_extra_doc_attributes]
pub struct CLISpec(pub String);

impl From<&str> for CLISpec {
  fn from(value: &str) -> Self {
    Self(value.to_string())
  }
}

impl CLISpec {
  /// Construct a cli spec from a [str].
  pub fn new<R: AsRef<str>>(r: R) -> Self {
    Self(r.as_ref().to_string())
  }
}

/// Errors executing spack commands.
#[derive(Debug, Display, Error)]
pub enum CommandError {
  /* FIXME: make pub trait ConfigCommand(.as_config() -> Config) to have only one error per command type!! */
  /// config error from {0:?}: {1}
  ConfigGetCompilers(config::GetCompilers, #[source] config::ConfigError),
  /// find error from {0:?}: {1}
  Find(find::Find, #[source] find::FindError),
  /// find prefix error from {0:?}: {1}
  FindPrefix(find::FindPrefix, #[source] find::FindError),
  /// load error from {0:?}: {1}
  Load(load::Load, #[source] load::LoadError),
  /// install error from {0:?}: {1}
  Install(install::Install, #[source] install::InstallError),
  /// build env error from {0:?}: {1}
  BuildEnv(build_env::BuildEnv, #[source] build_env::BuildEnvError),
  /// compiler-find error from {0:?}: {1}
  CompilerFind(
    compiler_find::CompilerFind,
    #[source] compiler_find::CompilerFindError,
  ),
  /// find compiler specs error from {0:?}: {1}
  FindCompilerSpecs(
    compiler_find::FindCompilerSpecs,
    #[source] compiler_find::CompilerFindError,
  ),
}

pub mod config {
  use super::*;
  use crate::{
    invocation::command::{
      self,
      sync::{Output, SyncInvocable},
      CommandBase,
    },
    Invocation,
  };

  use lazy_static::lazy_static;
  use serde::{Deserialize, Serialize};
  use serde_yaml;

  use std::fmt::Debug;

  /// Errors manipulating config.
  #[derive(Debug, Display, Error)]
  pub enum ConfigError {
    /// command error: {0}
    Command(#[from] command::CommandErrorWrapper),
    /// yaml error {0}
    Yaml(#[from] serde_yaml::Error),
    /// error manipulating yaml object {0}: {1}
    YamlManipulation(String, &'static str),
  }

  impl ConfigError {
    pub fn yaml_manipulation<D: Debug>(yaml_source: D, msg: &'static str) -> Self {
      Self::YamlManipulation(format!("{:?}", yaml_source), msg)
    }
  }

  #[derive(Debug, Clone)]
  pub struct Config {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// The scope to request the config be drawn from.
    pub scope: Option<String>,
  }

  impl CommandBase for Config {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      let Self { spack, scope } = self;
      let scope_args = if let Some(scope) = &scope {
        vec!["--scope", scope]
      } else {
        vec![]
      };
      let argv = command::Argv(
        ["config"]
          .into_iter()
          .chain(scope_args.into_iter())
          .map(|s| s.to_string())
          .chain(argv.0.into_iter())
          .collect(),
      );
      Ok(spack.hydrate_command(argv)?)
    }
  }

  /// Request to execute `spack config get "$self.section"` and parse the YAML output.
  #[derive(Debug, Clone)]
  struct Get {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// The scope to request the config be drawn from.
    pub scope: Option<String>,
    /// Section name to print.
    pub section: String,
  }

  impl CommandBase for Get {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      /* We do not accept any additional arguments for this command! */
      argv.drop_empty();
      let Self {
        spack,
        scope,
        section,
      } = self;
      let args: command::Argv = ["get", &section].as_ref().into();
      Ok(Config { spack, scope }.hydrate_command(args)?)
    }
  }

  /// Paths to specific executables this compiler owns.
  #[derive(Debug, Display, Serialize, Deserialize, Clone)]
  pub struct CompilerPaths {
    /// Path to the C compiler.
    pub cc: Option<PathBuf>,
    /// Path to the C++ compiler.
    pub cxx: Option<PathBuf>,
    /// Path to the FORTRAN 77 compiler.
    pub f77: Option<PathBuf>,
    /// Path to the fortran 90 compiler.
    pub fc: Option<PathBuf>,
  }

  /// A single compiler's spec from running [`GetCompilers::get_compilers`].
  #[derive(Debug, Display, Serialize, Deserialize, Clone)]
  pub struct CompilerSpec {
    /// Spec string that can be used to select the given compiler after a `%` in a [`CLISpec`].
    pub spec: String,
    /// Paths which could be located for this compiler.
    pub paths: CompilerPaths,
    flags: serde_yaml::Value,
    operating_system: String,
    target: String,
    modules: serde_yaml::Value,
    environment: serde_yaml::Value,
    extra_rpaths: serde_yaml::Value,
  }

  /// Request to execute `spack config get compilers` and parse the YAML output.
  #[derive(Debug, Clone)]
  pub struct GetCompilers {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// The scope to request the config be drawn from.
    pub scope: Option<String>,
  }

  impl CommandBase for GetCompilers {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      let Self { spack, scope } = self;
      Ok(
        Get {
          spack,
          scope,
          section: "compilers".to_string(),
        }
        .hydrate_command(argv)?,
      )
    }
  }

  impl GetCompilers {
    /// Execute `spack config get compilers` and parse the YAML output.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{
    ///   Invocation,
    ///   commands::{*, config::*},
    ///   invocation::command::{Command, sync::SyncInvocable},
    /// };
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await?;
    ///
    /// // .get_compilers() will return an array of compiler specs.
    /// let get_compilers = GetCompilers { spack, scope: None };
    /// let found_compilers = get_compilers.clone().get_compilers().await
    ///   .map_err(|e| CommandError::ConfigGetCompilers(get_compilers, e))?;
    /// assert!(!found_compilers.is_empty());
    ///
    /// // Get the path to a working C compiler and check that it can executed.
    /// let first_cc = found_compilers[0].paths.cc
    ///   .as_ref()
    ///   .expect("cc should have been defined")
    ///   .clone();
    /// let command = Command {
    ///   exe: first_cc, argv: ["--version"].as_ref().into(),
    ///   ..Default::default()
    /// };
    /// let output = command.invoke().await.expect("cc --version should have succeeded");
    /// assert!(!output.stdout.is_empty());
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn get_compilers(self) -> Result<Vec<CompilerSpec>, ConfigError> {
      let command = self.hydrate_command(command::Argv::empty())?;
      let Output { stdout } = command.invoke().await?;

      let top_level: serde_yaml::Value = serde_yaml::from_slice(&stdout)?;
      lazy_static! {
        static ref TOP_LEVEL_KEY: serde_yaml::Value =
          serde_yaml::Value::String("compilers".to_string());
        static ref SECOND_KEY: serde_yaml::Value =
          serde_yaml::Value::String("compiler".to_string());
      }
      let compiler_objects: Vec<&serde_yaml::Value> = top_level
        .as_mapping()
        .and_then(|m| m.get(&TOP_LEVEL_KEY))
        .and_then(|c| c.as_sequence())
        .ok_or_else(|| {
          ConfigError::yaml_manipulation(
            &top_level,
            "expected top-level YAML to be a mapping with key 'compilers'",
          )
        })?
        .iter()
        .map(|o| {
          o.as_mapping()
            .and_then(|c| c.get(&SECOND_KEY))
            .ok_or_else(|| {
              ConfigError::yaml_manipulation(
                o,
                "expected 'compilers' entries to be mappings with key 'compiler'",
              )
            })
        })
        .collect::<Result<Vec<_>, _>>()?;
      let compiler_specs: Vec<CompilerSpec> = compiler_objects
        .into_iter()
        .map(|v| serde_yaml::from_value(v.clone()))
        .collect::<Result<Vec<CompilerSpec>, _>>()?;

      Ok(compiler_specs)
    }
  }
}

/// Find command.
pub mod find {
  use super::*;
  use crate::{
    invocation::command::{
      self,
      sync::{Output, SyncInvocable},
      CommandBase,
    },
    Invocation,
  };

  use lazy_static::lazy_static;
  use regex::Regex;
  use serde::{Deserialize, Serialize};
  use serde_json;

  use std::str;

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

  /// A concrete version string from [FoundSpec::version].
  #[derive(Debug, Display, Serialize, Deserialize, Clone)]
  pub struct ConcreteVersion(pub String);

  /// Errors finding.
  #[derive(Debug, Display, Error)]
  pub enum FindError {
    /// command line error {0}
    Command(#[from] command::CommandErrorWrapper),
    /// installation error {0}
    Install(#[from] install::InstallError),
    /// json error {0}
    Json(#[from] serde_json::Error),
    /// unknown error: {0}
    Unknown(String),
  }

  /// Find request.
  #[derive(Debug, Clone)]
  pub struct Find {
    pub spack: Invocation,
    pub spec: CLISpec,
  }

  impl CommandBase for Find {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      /* We do not accept any additional arguments for this command! */
      argv.drop_empty();
      let Self { spack, spec } = self;
      let args = command::Argv(
        ["find", "--json", &spec.0]
          .into_iter()
          .map(|s| s.to_string())
          .collect(),
      );
      Ok(spack.hydrate_command(args)?)
    }
  }

  impl Find {
    /// Execute `spack find "$self.spec"`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, install::*, find::*}, Invocation};
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await?;
    ///
    /// // Ensure a python is installed that is at least version 3.
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("python@3:") };
    /// let found_spec = install.clone().install_find().await.unwrap();
    ///
    /// // Look for a python spec with that exact hash.
    /// let find = Find { spack, spec: found_spec.hashed_spec() };
    ///
    /// // .find() will return an array of values, which may have any length.
    /// let found_specs = find.clone().find().await
    ///   .map_err(|e| spack::commands::CommandError::Find(find, e))?;
    ///
    /// // Here, we just check the first of the found specs.
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
      let command = self.hydrate_command(command::Argv::empty())?;
      let command::sync::Output { stdout } = command.invoke().await?;

      match serde_json::from_slice::<'_, serde_json::Value>(&stdout)? {
        serde_json::Value::Array(values) => {
          let found_specs: Vec<FoundSpec> = values
            .into_iter()
            .map(|v| serde_json::from_value(v))
            .collect::<Result<Vec<FoundSpec>, _>>()?;
          Ok(found_specs)
        }
        value => Err(FindError::Unknown(format!(
          "unable to parse find output: {:?}",
          value
        ))),
      }
    }
  }

  /// Find prefix request.
  #[derive(Debug, Clone)]
  pub struct FindPrefix {
    pub spack: Invocation,
    pub spec: CLISpec,
  }

  impl CommandBase for FindPrefix {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      /* We do not accept any additional arguments for this command! */
      argv.drop_empty();
      let Self { spack, spec } = self;
      let args = command::Argv(
        ["find", "--no-groups", "-p", spec.0.as_ref()]
          .map(|s| s.to_string())
          .into_iter()
          .collect(),
      );
      Ok(spack.hydrate_command(args)?)
    }
  }

  impl FindPrefix {
    /// Execute `spack find -p "$self.spec"`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use std::fs;
    /// use spack::{commands::{*, install::*, find::*}, Invocation};
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await?;
    ///
    /// // Ensure a python is installed that is at least version 3.
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("python@3:") };
    /// let found_spec = install.clone().install_find().await
    ///   .map_err(|e| spack::commands::CommandError::Install(install, e))?;
    ///
    /// // Look for a python spec with that exact hash.
    /// let find_prefix = FindPrefix { spack, spec: found_spec.hashed_spec() };
    ///
    /// // .find_prefix() will return the spec's prefix root wrapped in an Option.
    /// let python_prefix = find_prefix.clone().find_prefix().await
    ///   .map_err(|e| spack::commands::CommandError::FindPrefix(find_prefix, e))?
    ///   .unwrap();
    ///
    /// // Verify that this prefix contains the python3 executable.
    /// let python3_exe = python_prefix.join("bin").join("python3");
    /// assert!(fs::File::open(python3_exe).is_ok());
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn find_prefix(self) -> Result<Option<PathBuf>, FindError> {
      let spec = self.spec.clone();
      let command = self.hydrate_command(command::Argv::empty())?;

      match command.invoke().await {
        Ok(Output { stdout }) => {
          lazy_static! {
            static ref FIND_PREFIX_REGEX: Regex =
              Regex::new(r"^([^@]+)@([^ ]+) +([^ ].*)\n$").unwrap();
          }
          let stdout = str::from_utf8(&stdout).map_err(|e| {
            FindError::Unknown(format!("failed to parse utf8 ({}): got {:?}", e, &stdout))
          })?;
          let m = FIND_PREFIX_REGEX.captures(&stdout).unwrap();
          let name = m.get(1).unwrap().as_str();
          /* FIXME: this method should be using a custom `spack python` script!! */
          assert!(spec.0.starts_with(name));
          let prefix: PathBuf = m.get(3).unwrap().as_str().into();
          Ok(Some(prefix))
        }
        Err(command::CommandErrorWrapper {
          output: Some(Output { stdout }),
          error: command::CommandError::NonZeroExit(1),
          ..
        }) if stdout.starts_with(b"==> No package matches") => Ok(None),
        Err(e) => Err(e.into()),
      }
    }
  }
}

/// Load command.
pub mod load {
  use super::*;
  use crate::{
    invocation::{
      command::{self, sync::SyncInvocable, CommandBase},
      env::LoadEnvironment,
    },
    Invocation,
  };

  use std::str;

  /// Errors loading.
  #[derive(Debug, Display, Error)]
  pub enum LoadError {
    /// command error: {0}
    Command(#[from] command::CommandErrorWrapper),
    /// utf8 decoding error: {0}
    Utf8(#[from] str::Utf8Error),
  }

  /// Load request.
  #[derive(Debug, Clone)]
  pub struct Load {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// Specs to load the environment for.
    pub specs: Vec<CLISpec>,
  }

  impl CommandBase for Load {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      /* We do not accept any additional arguments for this command! */
      argv.drop_empty();
      let Self { spack, specs } = self;
      let args = command::Argv(
        ["load", "--sh"]
          .into_iter()
          .map(|s| s.to_string())
          .chain(specs.into_iter().map(|s| s.0))
          .collect(),
      );
      Ok(spack.hydrate_command(args)?)
    }
  }

  impl Load {
    /// Execute `spack load --sh "$self.spec"`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, install::*, load::*}, Invocation};
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await?;
    ///
    /// // Ensure a python is installed that is at least version 3.
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("python@3:") };
    /// let found_spec = install.clone().install_find().await.unwrap();
    ///
    /// // Look for a python spec with that exact hash.
    /// let load = Load { spack, specs: vec![found_spec.hashed_spec()] };
    /// let python_env = load.clone().load().await
    ///   .map_err(|e| spack::commands::CommandError::Load(load, e))?;
    /// // This is the contents of a source-able environment script.
    /// assert!(python_env.0.starts_with("export ACLOCAL_PATH="));
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn load(self) -> Result<LoadEnvironment, LoadError> {
      let command = self.hydrate_command(command::Argv::empty())?;
      let command::sync::Output { stdout } = command.invoke().await?;

      Ok(LoadEnvironment(str::from_utf8(&stdout)?.to_string()))
    }
  }
}

/// Install command.
pub mod install {
  use super::{find::*, *};
  use crate::{
    invocation::{
      command::{self, stream::Streamable, CommandBase},
      env,
    },
    Invocation,
  };

  /// Errors installing.
  #[derive(Debug, Display, Error)]
  pub enum InstallError {
    /// {0}
    Inner(#[source] Box<CommandError>),
    /// spack command error {0}
    Command(#[from] command::CommandErrorWrapper),
  }

  /// Install request.
  #[derive(Debug, Clone)]
  pub struct Install {
    pub spack: Invocation,
    pub spec: CLISpec,
  }

  impl CommandBase for Install {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      let Self { spack, spec } = self;

      /* Generate spack argv. */
      let argv = command::Argv(
        ["install"]
          .into_iter()
          .map(|s| s.to_string())
          /* Add any additional parameters to spack install (such as '--verbose') via `argv`. */
          .chain(argv.0.into_iter())
          .chain([spec.0.clone()].into_iter())
          .collect(),
      );
      Ok(spack.hydrate_command(argv)?)
    }
  }

  impl Install {
    /// Execute [`Self::install`], then execute [`Find::find`].
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, install::*}, Invocation};
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await?;
    ///
    /// // Install libiberty, if we don't have it already!
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("libiberty@2.37") };
    /// let found_spec = install.clone().install_find().await
    ///   .map_err(|e| spack::commands::CommandError::Install(install, e))?;
    ///
    /// // The result matches our query!
    /// assert!(&found_spec.name == "libiberty");
    /// assert!(&found_spec.version.0 == "2.37");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn install_find(self) -> Result<FoundSpec, InstallError> {
      let Self { spack, spec } = self.clone();

      /* Check if the spec already exists. */
      let cached_find = Find {
        spack: spack.clone(),
        spec: spec.clone(),
      };
      /* FIXME: ensure we have a test for both cached and uncached!!! */
      if let Ok(found_specs) = cached_find.find().await {
        return Ok(found_specs[0].clone());
      }

      self.install().await?;

      /* Find the first match for the spec we just tried to install. */
      /* NB: this will probably immediately break if the CLI spec covers more than one concrete
       * spec! For now we just take the first result!! */
      let find = Find { spack, spec };
      let found_specs = find
        .clone()
        .find()
        .await
        .map_err(|e| CommandError::Find(find, e))
        .map_err(|e| InstallError::Inner(Box::new(e)))?;
      Ok(found_specs[0].clone())
    }

    /// Execute `spack install "$self.spec"`, piping stdout and stderr to the terminal.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, install::*}, Invocation};
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await?;
    ///
    /// // Install libiberty, if we don't have it already!
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("libiberty@2.37") };
    /// let found_spec = install.clone().install_find().await
    ///   .map_err(|e| spack::commands::CommandError::Install(install, e))?;
    ///
    /// // The result matches our query!
    /// assert!(&found_spec.name == "libiberty");
    /// assert!(&found_spec.version.0 == "2.37");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn install(self) -> Result<(), InstallError> {
      let command = self.hydrate_command(
        [
          "--verbose",
          "--fail-fast",
          /* FIXME: determine appropriate amount of build parallelism! */
          "-j16",
        ]
        .as_ref()
        .into(),
      )?;

      /* Kick off the child process, reading its streams asynchronously. */
      let streaming = command.invoke_streaming()?;
      streaming.wait().await?;

      Ok(())
    }

    /// Do [`Self::install`], but after sourcing the contents of `load_env`.
    ///
    /// FIXME: DOCUMENT AND TEST!!
    pub async fn install_with_env(
      self,
      load_env: env::LoadEnvironment,
    ) -> Result<(), InstallError> {
      let Self { spack, spec } = self;
      let env_inv = env::EnvInvocation {
        inner: spack,
        load_env,
      };
      let command = env_inv.hydrate_command(
        ["install", "--verbose", "--fail-fast", "-j16", &spec.0]
          .as_ref()
          .into(),
      )?;
      let streaming = command.invoke_streaming()?;
      streaming.wait().await?;

      Ok(())
    }
  }
}

/// Build-env command.
pub mod build_env {
  use super::*;
  use crate::{
    invocation::command::{
      self,
      sync::{Output, SyncInvocable},
      CommandBase,
    },
    Invocation,
  };

  use std::path::PathBuf;

  /// Errors setting up the build environment.
  #[derive(Debug, Display, Error)]
  pub enum BuildEnvError {
    /// {0}
    Command(#[from] command::CommandErrorWrapper),
    /// install error {0}
    Install(#[from] install::InstallError),
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
    pub argv: command::Argv,
  }

  impl CommandBase for BuildEnv {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      eprintln!("BuildEnv");
      dbg!(&self);
      dbg!(&argv);
      let Self {
        spack,
        spec,
        argv,
        dump,
      } = self;

      let dump_args = if let Some(d) = dump {
        vec!["--dump".to_string(), format!("{}", d.display())]
      } else {
        vec![]
      };

      let argv = command::Argv(
        ["build-env".to_string()]
          .into_iter()
          .chain(dump_args.into_iter())
          .chain([spec.0].into_iter())
          .chain(argv.trailing_args().0.into_iter())
          .collect(),
      );

      Ok(spack.hydrate_command(argv)?)
    }
  }

  impl BuildEnv {
    /// Execute `spack build-env "$self.spec" -- $self.argv`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// let td = tempdir::TempDir::new("spack-summon-test").unwrap();
    /// use std::{fs, io::BufRead};
    /// use spack::{
    ///   Invocation,
    ///   commands::{*, build_env::*, install::*},
    ///   invocation::{command::{*, sync::Output}},
    /// };
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await?;
    ///
    /// // Let's get a python 3 or later installed!
    /// let install = Install { spack: spack.clone(), spec: CLISpec::new("python@3:") };
    /// let found_spec = install.clone().install_find().await
    ///   .map_err(|e| spack::commands::CommandError::Install(install, e))?;
    ///
    /// // Now let's activate the build environment for it!
    /// let build_env = BuildEnv {
    ///   spack: spack.clone(),
    ///   // Use the precise spec we just ensured was installed.
    ///   spec: found_spec.hashed_spec(),
    ///   dump: None,
    ///   argv: Argv::empty(),
    /// };
    /// // Execute build-env to get an env printed to stdout.
    /// let output = build_env.clone().build_env().await
    ///   .map_err(|e| spack::commands::CommandError::BuildEnv(build_env, e))?;
    ///
    /// // Example ad-hoc parsing of environment source files.
    /// let mut spec_was_found: bool = false;
    /// for line in output.stdout.lines() {
    ///   let line = line.unwrap();
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
    ///   argv: Argv::empty(),
    /// };
    /// // We will have written to ./.env-dump!
    /// let _ = build_env.clone().build_env().await
    ///   .map_err(|e| spack::commands::CommandError::BuildEnv(build_env, e))?;
    /// spec_was_found = false;
    /// for line in fs::read_to_string(&dump).expect(".env-dump was created").lines() {
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
    /// let Output { stdout } = build_env.clone().build_env().await
    ///   .map_err(|e| spack::commands::CommandError::BuildEnv(build_env, e))?;
    /// assert!(&stdout[..6] == b"python");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn build_env(self) -> Result<Output, BuildEnvError> {
      let command = self.hydrate_command(command::Argv::empty())?;
      let output = command.invoke().await?;
      Ok(output)
    }
  }
}

/// spack python command.
pub mod python {
  use super::*;
  use crate::{
    invocation::command::{self, CommandBase},
    Invocation,
  };

  use tempfile::{NamedTempFile, TempPath};

  /// spack python command request.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use std::str;
  /// use futures_lite::io::AsyncReadExt;
  /// use spack::{
  ///   Invocation,
  ///   commands::python::*,
  ///   invocation::{command::{*, sync::{Output, SyncInvocable}, stream::Streamable}},
  /// };
  ///
  /// // Locate all the executables.
  /// let spack = Invocation::summon().await.unwrap();
  ///
  /// // Create python execution request.
  /// let spack_python = SpackPython {
  ///   spack: spack.clone(),
  ///   script: "import spack; print(spack.__version__)".to_string(),
  /// };
  /// let command = spack_python.hydrate_command(Argv::empty()).expect("hydration failed");
  ///
  /// // Spawn the child process and wait for it to end.
  /// let Output { stdout } = command.clone().invoke().await.expect("sync command failed");
  /// // Parse stdout into utf8...
  /// let version = str::from_utf8(&stdout).unwrap()
  ///   // ...and strip the trailing newline...
  ///   .strip_suffix("\n").unwrap();
  /// // ...to verify it matches `spack.version`.
  /// assert!(version == &spack.version);
  ///
  /// // Spawn the child process and wait for it to end.
  /// let mut streaming = command.invoke_streaming().expect("streaming command invocation failed");
  ///
  /// // Slurp stdout all at once into a string.
  /// let mut version: String = "".to_string();
  /// streaming.stdout.read_to_string(&mut version).await.unwrap();
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
  pub struct SpackPython {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// The contents of the python script to execute.
    pub script: String,
  }

  impl SpackPython {
    fn write_python_script(script: String) -> io::Result<TempPath> {
      /* Create the script. */
      let (mut script_file, script_path) = NamedTempFile::new()?.into_parts();
      script_file.write_all(script.as_bytes())?;
      script_file.sync_all()?;
      /* Close the file, but keep the path alive. */
      Ok(script_path)
    }
  }

  impl CommandBase for SpackPython {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      eprintln!("SpackPython");
      dbg!(&self);
      dbg!(&argv);
      let Self { spack, script } = self;

      /* Create the script. */
      let command = spack.clone().hydrate_command(argv.clone())?;
      let script_path =
        Self::write_python_script(script).map_err(|e| command::CommandErrorWrapper {
          command,
          output: None,
          error: e.into(),
        })?;

      /* Craft the command line. */
      let argv = command::Argv(
        ["python".to_string(), format!("{}", script_path.display())]
          .into_iter()
          .chain(argv.as_strs().into_iter().map(|s| s.to_string()))
          .collect(),
      );
      let command = spack.hydrate_command(argv)?;

      /* FIXME: We don't ever delete the script! */
      script_path.keep().unwrap();

      Ok(command)
    }
  }
}

/// Compiler-find command.
pub mod compiler_find {
  use super::*;
  use crate::{
    invocation::command::{
      self,
      sync::{Output, SyncInvocable},
      CommandBase,
    },
    Invocation,
  };

  use serde::{Deserialize, Serialize};
  use serde_json;

  use std::{io, path::PathBuf};

  /// Errors locating a compiler.
  #[derive(Debug, Display, Error)]
  pub enum CompilerFindError {
    /// command line error {0}
    Command(#[from] command::CommandErrorWrapper),
    /// io error {0}
    Io(#[from] io::Error),
    /// json error {0}
    Json(#[from] serde_json::Error),
    /// unknown error: {0}
    Unknown(String),
  }

  /// Compiler-find request.
  #[derive(Debug, Clone)]
  pub struct CompilerFind {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// Paths to search for compilers in.
    pub paths: Vec<PathBuf>,
  }

  impl CommandBase for CompilerFind {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      /* We do not accept any additional arguments for this command! */
      argv.drop_empty();
      let Self { spack, paths } = self;
      let args = command::Argv(
        ["compiler", "find"]
          .map(|s| s.to_string())
          .into_iter()
          .chain(paths.into_iter().map(|p| format!("{}", p.display())))
          .collect(),
      );
      Ok(spack.hydrate_command(args)?)
    }
  }

  impl CompilerFind {
    /// Run `spack compiler find $self.paths`, without parsing the output.
    ///
    /// Use [`FindCompilerSpecs::find_compiler_specs`] to get information about the compilers spack
    /// can find.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, compiler_find::*}, Invocation};
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await.unwrap();
    ///
    /// // Create compiler-find execution request.
    /// let find_compiler_specs = FindCompilerSpecs {
    ///   spack: spack.clone(),
    ///   paths: vec![],
    /// };
    /// let found_compilers = find_compiler_specs.clone().find_compiler_specs().await
    ///   .map_err(|e| CommandError::FindCompilerSpecs(find_compiler_specs, e))?;
    /// // The first compiler on the list is clang!
    /// assert!(found_compilers[0].compiler.name.starts_with("clang"));
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn compiler_find(self) -> Result<(), CompilerFindError> {
      let command = self.hydrate_command(command::Argv::empty())?;
      let _ = command.invoke().await?;
      Ok(())
    }
  }

  #[derive(Debug, Clone)]
  pub struct FindCompilerSpecs {
    #[allow(missing_docs)]
    pub spack: Invocation,
    /// Paths to search for compilers in.
    pub paths: Vec<PathBuf>,
  }

  /// A compiler found by [`CompilerFind::compiler_find`].
  #[derive(Debug, Display, Serialize, Deserialize, Clone)]
  pub struct FoundCompiler {
    pub compiler: CompilerSpec,
  }

  #[derive(Debug, Display, Serialize, Deserialize, Clone)]
  pub struct CompilerSpec {
    pub name: String,
    pub version: String,
  }

  const COMPILER_SPEC_SOURCE: &str = include_str!("compiler-find.py");

  impl FindCompilerSpecs {
    /// Run a custom `spack python` script to print out compiler specs located in the given paths.
    ///
    /// If the given set of [`Self::paths`] is empty, use the defaults from config.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, compiler_find::*}, Invocation};
    ///
    /// // Locate all the executables.
    /// let spack = Invocation::summon().await.unwrap();
    ///
    /// // Create compiler-find execution request.
    /// let find_compiler_specs = FindCompilerSpecs {
    ///   spack: spack.clone(),
    ///   paths: vec![],
    /// };
    /// let found_compilers = find_compiler_specs.clone().find_compiler_specs().await
    ///   .map_err(|e| CommandError::FindCompilerSpecs(find_compiler_specs, e))?;
    /// // The first compiler on the list is clang!
    /// assert!(found_compilers[0].compiler.name.starts_with("clang"));
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn find_compiler_specs(self) -> Result<Vec<FoundCompiler>, CompilerFindError> {
      let command = self.hydrate_command(command::Argv::empty())?;
      let Output { stdout } = command.invoke().await?;

      match serde_json::from_slice::<'_, serde_json::Value>(&stdout)? {
        serde_json::Value::Array(values) => {
          let compiler_specs: Vec<FoundCompiler> = values
            .into_iter()
            .map(|v| serde_json::from_value(v))
            .collect::<Result<Vec<FoundCompiler>, _>>()?;
          Ok(compiler_specs)
        }
        value => Err(CompilerFindError::Unknown(format!(
          "unable to parse compiler-find.py output: {:?}",
          value
        ))),
      }
    }
  }

  impl CommandBase for FindCompilerSpecs {
    fn hydrate_command(
      self,
      argv: command::Argv,
    ) -> Result<command::Command, command::CommandErrorWrapper> {
      /* We do not accept any additional arguments for this command! */
      argv.drop_empty();
      let Self { spack, paths } = self.clone();

      let python = python::SpackPython {
        spack: spack.clone(),
        script: COMPILER_SPEC_SOURCE.to_string(),
      };
      let argv = command::Argv(
        paths
          .into_iter()
          .map(|p| format!("{}", p.display()))
          .collect(),
      );
      Ok(python.hydrate_command(argv)?)
    }
  }
}
