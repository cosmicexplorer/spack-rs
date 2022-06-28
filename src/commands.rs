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
  /// config error from {0:?}: {1}
  Config(config::Config, #[source] config::ConfigError),
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
  use crate::SpackInvocation;
  use super_process::{
    base::{self, CommandBase},
    exe,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use lazy_static::lazy_static;
  use serde::{Deserialize, Serialize};
  use serde_yaml;

  use std::{ffi::OsStr, fmt::Debug};

  /// Errors manipulating config.
  #[derive(Debug, Display, Error)]
  pub enum ConfigError {
    /// command error: {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// setup error: {0}
    Setup(#[from] base::SetupErrorWrapper),
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
    pub spack: SpackInvocation,
    /// The scope to request the config be drawn from.
    pub scope: Option<String>,
    pub passthrough: exe::Argv,
  }

  pub trait ConfigCommand {
    fn into_base_config(self) -> Config;
  }

  #[async_trait]
  impl CommandBase for Config {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self {
        spack,
        scope,
        passthrough,
      } = self;
      let scope_args = if let Some(scope) = &scope {
        vec!["--scope", scope]
      } else {
        vec![]
      };
      let argv = exe::Argv(
        ["config"]
          .into_iter()
          .chain(scope_args.into_iter())
          .map(|s| OsStr::new(s).to_os_string())
          .chain(passthrough.0.into_iter())
          .collect(),
      );
      Ok(
        spack
          .with_spack_exe(exe::Command {
            argv,
            ..Default::default()
          })
          .setup_command()
          .await?,
      )
    }
  }

  /// Request to execute `spack config get "$self.section"` and parse the YAML output.
  #[derive(Debug, Clone)]
  struct Get {
    #[allow(missing_docs)]
    pub spack: SpackInvocation,
    /// The scope to request the config be drawn from.
    pub scope: Option<String>,
    /// Section name to print.
    pub section: String,
  }

  impl ConfigCommand for Get {
    fn into_base_config(self) -> Config {
      let Self {
        spack,
        scope,
        section,
      } = self;
      Config {
        spack,
        scope,
        passthrough: ["get", &section].into(),
      }
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
    pub spack: SpackInvocation,
    /// The scope to request the config be drawn from.
    pub scope: Option<String>,
  }

  impl ConfigCommand for GetCompilers {
    fn into_base_config(self) -> Config {
      let Self { spack, scope } = self;
      let get = Get {
        spack,
        scope,
        section: "compilers".to_string(),
      };
      get.into_base_config()
    }
  }

  impl GetCompilers {
    /// Execute `spack config get compilers` and parse the YAML output.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use super_process::{exe, sync::SyncInvocable};
    /// use spack::{SpackInvocation, commands::{CommandError, config::*}};
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await?;
    ///
    /// // .get_compilers() will return an array of compiler specs.
    /// let get_compilers = GetCompilers { spack, scope: None };
    /// let found_compilers = get_compilers.clone().get_compilers().await
    ///   .map_err(|e| CommandError::Config(get_compilers.into_base_config(), e))?;
    /// assert!(!found_compilers.is_empty());
    ///
    /// // Get the path to a working C compiler and check that it can executed.
    /// let first_cc: exe::Exe = found_compilers[0].paths.cc
    ///   .as_ref()
    ///   .expect("cc should have been defined")
    ///   .into();
    /// let command = exe::Command {
    ///   exe: first_cc, argv: ["--version"].into(),
    ///   ..Default::default()
    /// };
    /// let output = command.invoke().await.expect("cc --version should have succeeded");
    /// assert!(!output.stdout.is_empty());
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn get_compilers(self) -> Result<Vec<CompilerSpec>, ConfigError> {
      let config_request = self.into_base_config();
      let command = config_request
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in GetCompilers::get_compilers()")))?;
      let output = command.invoke().await?;

      let top_level: serde_yaml::Value = serde_yaml::from_slice(&output.stdout)?;
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
  use crate::{utils::prefix, SpackInvocation};
  use super_process::{
    base::{self, CommandBase},
    exe,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use lazy_static::lazy_static;
  use regex::Regex;
  use serde::{Deserialize, Serialize};
  use serde_json;

  use std::{ffi::OsStr, str};

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
    Command(#[from] exe::CommandErrorWrapper),
    /// setup error: {0}
    Setup(#[from] base::SetupErrorWrapper),
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
    pub spack: SpackInvocation,
    pub spec: CLISpec,
  }

  #[async_trait]
  impl CommandBase for Find {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self { spack, spec } = self;
      let args = exe::Argv(
        ["find", "--json", &spec.0]
          .into_iter()
          .map(|s| OsStr::new(s).to_os_string())
          .collect(),
      );
      Ok(
        spack
          .with_spack_exe(exe::Command {
            argv: args,
            ..Default::default()
          })
          .setup_command()
          .await?,
      )
    }
  }

  impl Find {
    /// Execute `spack find "$self.spec"`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, install::*, find::*}, SpackInvocation};
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await?;
    ///
    /// // Ensure a python is installed that is at least version 3.
    /// let install = Install {
    ///   spack: spack.clone(),
    ///   spec: CLISpec::new("python@3:"),
    ///   verbosity: Default::default(),
    /// };
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
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in Find::find()")))?;
      let output = command.invoke().await?;

      match serde_json::from_slice::<'_, serde_json::Value>(&output.stdout)? {
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
    pub spack: SpackInvocation,
    pub spec: CLISpec,
  }

  #[async_trait]
  impl CommandBase for FindPrefix {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self { spack, spec } = self;
      let args = exe::Argv(
        ["find", "--no-groups", "-p", spec.0.as_ref()]
          .map(|s| OsStr::new(s).to_os_string())
          .into_iter()
          .collect(),
      );
      Ok(
        spack
          .with_spack_exe(exe::Command {
            argv: args,
            ..Default::default()
          })
          .setup_command()
          .await?,
      )
    }
  }

  impl FindPrefix {
    /// Execute `spack find -p "$self.spec"`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use std::fs;
    /// use spack::{commands::{*, install::*, find::*}, SpackInvocation};
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await?;
    ///
    /// // Ensure a python is installed that is at least version 3.
    /// let install = Install {
    ///   spack: spack.clone(),
    ///   spec: CLISpec::new("python@3:"),
    ///   verbosity: Default::default(),
    /// };
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
    /// let python3_exe = python_prefix.path.join("bin").join("python3");
    /// assert!(fs::File::open(python3_exe).is_ok());
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn find_prefix(self) -> Result<Option<prefix::Prefix>, FindError> {
      let spec = self.spec.clone();
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in FindPrefix::find_prefix()")))?;

      match command.invoke().await {
        Ok(output) => {
          lazy_static! {
            static ref FIND_PREFIX_REGEX: Regex =
              Regex::new(r"^([^@]+)@([^ ]+) +([^ ].*)\n$").unwrap();
          }
          let stdout = str::from_utf8(&output.stdout).map_err(|e| {
            FindError::Unknown(format!("failed to parse utf8 ({}): got {:?}", e, &output))
          })?;
          let m = FIND_PREFIX_REGEX.captures(&stdout).unwrap();
          let name = m.get(1).unwrap().as_str();
          /* FIXME: this method should be using a custom `spack python` script!! */
          assert!(spec.0.starts_with(name));
          let prefix: PathBuf = m.get(3).unwrap().as_str().into();
          Ok(Some(prefix::Prefix { path: prefix }))
        }
        Err(exe::CommandErrorWrapper {
          context,
          error: exe::CommandError::NonZeroExit(1),
          ..
        }) if context.contains("==> No package matches") => Ok(None),
        Err(e) => Err(e.into()),
      }
    }
  }
}

/// Load command.
pub mod load {
  use super::*;
  use crate::SpackInvocation;
  use super_process::{
    base::{self, CommandBase},
    exe, sh,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;

  use std::{ffi::OsStr, str};

  /// Errors loading.
  #[derive(Debug, Display, Error)]
  pub enum LoadError {
    /// command error: {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// setup error: {0}
    Setup(#[from] base::SetupErrorWrapper),
    /// utf8 decoding error: {0}
    Utf8(#[from] str::Utf8Error),
    /// shell error {0}
    Shell(#[from] sh::ShellErrorWrapper),
  }

  /// Load request.
  #[derive(Debug, Clone)]
  pub struct Load {
    #[allow(missing_docs)]
    pub spack: SpackInvocation,
    /// Specs to load the environment for.
    pub specs: Vec<CLISpec>,
  }

  #[async_trait]
  impl CommandBase for Load {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self { spack, specs } = self;
      let args = exe::Argv(
        ["load", "--sh"]
          .into_iter()
          .map(|s| s.to_string())
          .chain(specs.into_iter().map(|s| s.0))
          .map(|s| OsStr::new(&s).to_os_string())
          .collect(),
      );
      Ok(
        spack
          .with_spack_exe(exe::Command {
            argv: args,
            ..Default::default()
          })
          .setup_command()
          .await?,
      )
    }
  }

  impl Load {
    /// Execute `spack load --sh "$self.spec"`.
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use std::ffi::OsStr;
    /// use super_process::exe;
    /// use spack::{commands::{*, install::*, load::*}, SpackInvocation};
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await?;
    ///
    /// // Ensure a python is installed that is at least version 3.
    /// let install = Install {
    ///   spack: spack.clone(),
    ///   spec: CLISpec::new("python@3:"),
    ///   verbosity: Default::default(),
    /// };
    /// let found_spec = install.clone().install_find().await.unwrap();
    ///
    /// // Look for a python spec with that exact hash.
    /// let load = Load { spack, specs: vec![found_spec.hashed_spec()] };
    /// let exe::EnvModifications(python_env) = load.clone().load().await
    ///   .map_err(|e| spack::commands::CommandError::Load(load, e))?;
    /// // This is the contents of a source-able environment script.
    /// assert!(python_env.contains_key(OsStr::new("ACLOCAL_PATH")));
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn load(self) -> Result<exe::EnvModifications, LoadError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in Load::load()")))?;
      let load_output = command.invoke().await?;

      let env = sh::EnvAfterScript {
        source: sh::ShellSource {
          contents: load_output.stdout,
        },
      }
      .extract_env_bindings()
      .await?;

      Ok(env)
    }
  }
}

/// Install command.
pub mod install {
  use super::{find::*, *};
  use crate::SpackInvocation;
  use super_process::{
    base::{self, CommandBase},
    exe,
    stream::Streamable,
  };

  use async_trait::async_trait;

  use std::ffi::OsStr;

  /// Errors installing.
  #[derive(Debug, Display, Error)]
  pub enum InstallError {
    /// {0}
    Inner(#[source] Box<CommandError>),
    /// spack command error {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// setup error: {0}
    Setup(#[from] base::SetupErrorWrapper),
  }

  #[derive(Debug, Display, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum InstallVerbosity {
    /// <standard verbosity>
    Standard,
    /// <with --verbose>
    Verbose,
  }

  impl Default for InstallVerbosity {
    fn default() -> Self {
      Self::Verbose
    }
  }

  impl InstallVerbosity {
    pub(crate) fn verbosity_args(self) -> Vec<String> {
      match self {
        Self::Standard => vec![],
        Self::Verbose => vec!["--verbose".to_string()],
      }
    }
  }

  /// Install request.
  #[derive(Debug, Clone)]
  pub struct Install {
    pub spack: SpackInvocation,
    pub spec: CLISpec,
    pub verbosity: InstallVerbosity,
  }

  #[async_trait]
  impl CommandBase for Install {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self {
        spack,
        spec,
        verbosity,
      } = self;

      /* Generate spack argv. */
      let argv = exe::Argv(
        /* FIXME: determine appropriate amount of build parallelism! */
        ["install", "--fail-fast", "-j16"]
          .into_iter()
          .map(|s| s.to_string())
          .chain(verbosity.verbosity_args().into_iter())
          .chain([spec.0.clone()].into_iter())
          .map(|s| OsStr::new(&s).to_os_string())
          .collect(),
      );
      Ok(
        spack
          .with_spack_exe(exe::Command {
            argv,
            ..Default::default()
          })
          .setup_command()
          .await?,
      )
    }
  }

  impl Install {
    /// Execute [`Self::install`], then execute [`Find::find`].
    ///```
    /// # fn main() -> Result<(), spack::Error> {
    /// # tokio_test::block_on(async {
    /// use spack::{commands::{*, install::*}, SpackInvocation};
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await?;
    ///
    /// // Install libiberty, if we don't have it already!
    /// let install = Install {
    ///   spack: spack.clone(),
    ///   spec: CLISpec::new("libiberty@2.37"),
    ///   verbosity: Default::default(),
    /// };
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
      let Self { spack, spec, .. } = self.clone();

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
    /// use spack::{commands::{*, install::*}, SpackInvocation};
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await?;
    ///
    /// // Install libiberty, if we don't have it already!
    /// let install = Install {
    ///   spack: spack.clone(),
    ///   spec: CLISpec::new("libiberty@2.37"),
    ///   verbosity: Default::default(),
    /// };
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
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in Install::install()")))?;

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
      load_env: exe::EnvModifications,
    ) -> Result<(), InstallError> {
      let mut command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in Install::install_with_env()")))?;
      command.env = load_env;

      let streaming = command.invoke_streaming()?;
      streaming.wait().await?;

      Ok(())
    }
  }
}

/// Build-env command.
pub mod build_env {
  use super::*;
  use crate::SpackInvocation;
  use super_process::{
    base::{self, CommandBase},
    exe,
    sync::{self, SyncInvocable},
  };

  use async_trait::async_trait;

  use std::{ffi::OsStr, path::PathBuf};

  /// Errors setting up the build environment.
  #[derive(Debug, Display, Error)]
  pub enum BuildEnvError {
    /// {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// setup error {0}
    Setup(#[from] base::SetupErrorWrapper),
    /// install error {0}
    Install(#[from] install::InstallError),
    /// io error: {0}
    Io(#[from] io::Error),
  }

  /// Build-env request.
  #[derive(Debug, Clone)]
  pub struct BuildEnv {
    #[allow(missing_docs)]
    pub spack: SpackInvocation,
    /// Which spec to get into the environment of.
    pub spec: CLISpec,
    /// Optional output file for sourcing environment modifications.
    pub dump: Option<PathBuf>,
    /// Optional command line to evaluate within the package environment.
    ///
    /// If this argv is empty, the contents of the environment are printed to stdout with `env`.
    pub argv: exe::Argv,
  }

  #[async_trait]
  impl CommandBase for BuildEnv {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      eprintln!("BuildEnv");
      dbg!(&self);
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

      let argv = exe::Argv(
        ["build-env".to_string()]
          .into_iter()
          .chain(dump_args.into_iter())
          .chain([spec.0].into_iter())
          .map(|s| OsStr::new(&s).to_os_string())
          .chain(argv.trailing_args().0.into_iter())
          .collect(),
      );

      let command = spack
        .with_spack_exe(exe::Command {
          argv,
          ..Default::default()
        })
        .setup_command()
        .await?;

      Ok(command)
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
    ///   SpackInvocation,
    ///   commands::{*, build_env::*, install::*},
    /// };
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await?;
    ///
    /// // Let's get a python 3 or later installed!
    /// let install = Install {
    ///   spack: spack.clone(),
    ///   spec: CLISpec::new("python@3:"),
    ///   verbosity: Default::default(),
    /// };
    /// let found_spec = install.clone().install_find().await
    ///   .map_err(|e| spack::commands::CommandError::Install(install, e))?;
    ///
    /// // Now let's activate the build environment for it!
    /// let build_env = BuildEnv {
    ///   spack: spack.clone(),
    ///   // Use the precise spec we just ensured was installed.
    ///   spec: found_spec.hashed_spec(),
    ///   dump: None,
    ///   argv: Default::default(),
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
    ///   argv: Default::default(),
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
    /// let output = build_env.clone().build_env().await
    ///   .map_err(|e| spack::commands::CommandError::BuildEnv(build_env, e))?;
    /// assert!(&output.stdout[..6] == b"python");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn build_env(self) -> Result<sync::RawOutput, BuildEnvError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in BuildEnv::build_env()")))?;
      let output = command.invoke().await?;
      Ok(output)
    }
  }
}

/// spack python command.
pub mod python {
  use super::*;
  use crate::subprocess::spack;
  use super_process::{
    base::{self, CommandBase},
    exe,
  };

  use async_trait::async_trait;
  use tempfile::{NamedTempFile, TempPath};

  use std::ffi::OsStr;

  /// spack python command request.
  ///```
  /// # fn main() -> Result<(), spack::Error> {
  /// # tokio_test::block_on(async {
  /// use futures_lite::io::AsyncReadExt;
  /// use super_process::{base::CommandBase, sync::SyncInvocable, stream::Streamable};
  /// use spack::{SpackInvocation, commands::python};
  ///
  /// // Locate all the executables.
  /// let spack = SpackInvocation::summon().await.unwrap();
  ///
  /// // Create python execution request.
  /// let spack_python = python::SpackPython {
  ///   spack: spack.clone(),
  ///   script: "import spack; print(spack.__version__)".to_string(),
  ///   passthrough: Default::default(),
  /// };
  /// let command = spack_python.setup_command().await.expect("hydration failed");
  ///
  /// // Spawn the child process and wait for it to complete.
  /// let output = command.clone().invoke().await.expect("sync command failed");
  /// // Parse output into UTF-8...
  /// let decoded = output.decode(command.clone()).expect("decoding failed");
  /// // ...and verify the version matches `spack.version`.
  /// let version = decoded.stdout.strip_suffix("\n").unwrap();
  /// assert!(version == &spack.version);
  ///
  /// // Spawn the child process and wait for it to end.
  /// let mut streaming = command.invoke_streaming().expect("streaming command subprocess failed");
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
    pub spack: spack::SpackInvocation,
    /// The contents of the python script to execute.
    pub script: String,
    pub passthrough: exe::Argv,
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

  #[async_trait]
  impl CommandBase for SpackPython {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      eprintln!("SpackPython");
      dbg!(&self);
      let Self {
        spack,
        script,
        passthrough,
      } = self;

      /* Create the script. */
      let script_path = Self::write_python_script(script)?;
      /* FIXME: the file is never deleted!! */
      let script_path = script_path
        .keep()
        .expect("no error avoiding drop of temp file");

      /* Craft the command line. */
      let argv = exe::Argv(
        [OsStr::new("python"), OsStr::new(&script_path)]
          .into_iter()
          .map(|s| s.to_os_string())
          .chain(passthrough.0.into_iter())
          .collect(),
      );
      let command = spack
        .with_spack_exe(exe::Command {
          argv,
          ..Default::default()
        })
        .setup_command()
        .await?;

      Ok(command)
    }
  }
}

/// Compiler-find command.
pub mod compiler_find {
  use super::*;
  use crate::SpackInvocation;
  use super_process::{
    base::{self, CommandBase},
    exe,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use serde::{Deserialize, Serialize};
  use serde_json;

  use std::{ffi::OsStr, io, path::PathBuf};

  /// Errors locating a compiler.
  #[derive(Debug, Display, Error)]
  pub enum CompilerFindError {
    /// command line error {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// setup error {0}
    Setup(#[from] base::SetupErrorWrapper),
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
    pub spack: SpackInvocation,
    /// Paths to search for compilers in.
    pub paths: Vec<PathBuf>,
  }

  #[async_trait]
  impl CommandBase for CompilerFind {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self { spack, paths } = self;
      let args = exe::Argv(
        ["compiler", "find"]
          .map(|s| s.to_string())
          .into_iter()
          .chain(paths.into_iter().map(|p| format!("{}", p.display())))
          .map(|s| OsStr::new(&s).to_os_string())
          .collect(),
      );
      Ok(
        spack
          .with_spack_exe(exe::Command {
            argv: args,
            ..Default::default()
          })
          .setup_command()
          .await?,
      )
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
    /// use spack::{commands::{*, compiler_find::*}, SpackInvocation};
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await.unwrap();
    ///
    /// // Create compiler-find execution request.
    /// let find_compiler_specs = FindCompilerSpecs {
    ///   spack: spack.clone(),
    ///   paths: vec![],
    /// };
    /// let found_compilers = find_compiler_specs.clone().find_compiler_specs().await
    ///   .map_err(|e| CommandError::FindCompilerSpecs(find_compiler_specs, e))?;
    /// // The first compiler on the list is gcc or clang!
    /// let first_name = &found_compilers[0].compiler.name;
    /// assert!(first_name.starts_with("gcc") || first_name.starts_with("clang"));
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn compiler_find(self) -> Result<(), CompilerFindError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in compiler_find()!")))?;
      let _ = command.invoke().await?;
      Ok(())
    }
  }

  #[derive(Debug, Clone)]
  pub struct FindCompilerSpecs {
    #[allow(missing_docs)]
    pub spack: SpackInvocation,
    /// Paths to search for compilers in.
    pub paths: Vec<PathBuf>,
  }

  /// A compiler found by [`CompilerFind::compiler_find`].
  #[derive(Debug, Display, Serialize, Deserialize, Clone)]
  pub struct FoundCompiler {
    pub compiler: CompilerSpec,
  }

  impl FoundCompiler {
    pub fn into_compiler_spec_string(self) -> String {
      let Self {
        compiler: CompilerSpec { name, version },
      } = self;
      format!("{}@{}", name, version)
    }
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
    /// use spack::{commands::{*, compiler_find::*}, SpackInvocation};
    ///
    /// // Locate all the executables.
    /// let spack = SpackInvocation::summon().await.unwrap();
    ///
    /// // Create compiler-find execution request.
    /// let find_compiler_specs = FindCompilerSpecs {
    ///   spack: spack.clone(),
    ///   paths: vec![],
    /// };
    /// let found_compilers = find_compiler_specs.clone().find_compiler_specs().await
    ///   .map_err(|e| CommandError::FindCompilerSpecs(find_compiler_specs, e))?;
    /// // The first compiler on the list is gcc or clang!
    /// let first_name = &found_compilers[0].compiler.name;
    /// assert!(first_name.starts_with("gcc") || first_name.starts_with("clang"));
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn find_compiler_specs(self) -> Result<Vec<FoundCompiler>, CompilerFindError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context(format!("in find_compiler_specs()!")))?;
      let output = command.invoke().await?;

      match serde_json::from_slice::<'_, serde_json::Value>(&output.stdout)? {
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

  #[async_trait]
  impl CommandBase for FindCompilerSpecs {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self { spack, paths } = self.clone();

      let argv = exe::Argv(
        paths
          .into_iter()
          .map(|p| format!("{}", p.display()))
          .map(|s| OsStr::new(&s).to_os_string())
          .collect(),
      );
      let python = python::SpackPython {
        spack: spack.clone(),
        script: COMPILER_SPEC_SOURCE.to_string(),
        passthrough: argv,
      };
      Ok(python.setup_command().await?)
    }
  }
}
