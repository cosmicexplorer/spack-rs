/* copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking specific spack commands.

use super_process::exe::Argv;

use displaydoc::Display;
use thiserror::Error;

use std::{
  ffi::{OsStr, OsString},
  io::{self, Write},
  path::PathBuf,
};

/// {0}
///
/// An (abstract *or* concrete) spec string for a command-line argument. This is
/// used in [`find::Find::find`] to resolve concrete specs from the string.
#[derive(Debug, Display, Clone)]
#[ignore_extra_doc_attributes]
pub struct CLISpec(pub String);

impl From<&str> for CLISpec {
  fn from(value: &str) -> Self { Self(value.to_string()) }
}

impl CLISpec {
  /// Construct a cli spec from a [str].
  pub fn new<R: AsRef<str>>(r: R) -> Self { Self(r.as_ref().to_string()) }
}

pub trait ArgvWrapper {
  fn modify_argv(self, args: &mut Argv);
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct EnvName(pub String);

impl ArgvWrapper for EnvName {
  fn modify_argv(self, args: &mut Argv) {
    args.unshift(OsString::from(self.0));
    args.unshift(OsStr::new("--env").to_os_string());
  }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RepoDirs(pub Vec<PathBuf>);

/* FIXME: figure out how to fix if ^C hit during env install! */
impl ArgvWrapper for RepoDirs {
  fn modify_argv(mut self, args: &mut Argv) {
    if self.0.is_empty() {
      return;
    }
    assert!(self.0.iter().all(|p| p.is_absolute()));
    self.0.push("$spack/var/spack/repos/builtin".into());
    let joined = self
      .0
      .into_iter()
      .chain([])
      .map(|p| format!("{}", p.display()))
      .collect::<Vec<_>>()
      .join(",");
    let config_arg = format!("repos:[{}]", joined);
    args.unshift(OsString::from(config_arg));
    args.unshift(OsStr::new("-c").to_os_string());
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
  use once_cell::sync::Lazy;
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
          .chain(scope_args)
          .map(|s| OsStr::new(s).to_os_string())
          .chain(passthrough.0)
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

  /// Request to execute `spack config get "$self.section"` and parse the YAML
  /// output.
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
    /// Spec string that can be used to select the given compiler after a `%` in
    /// a [`CLISpec`].
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
    pub async fn get_compilers(self) -> Result<Vec<CompilerSpec>, ConfigError> {
      let config_request = self.into_base_config();
      let command = config_request
        .setup_command()
        .await
        .map_err(|e| e.with_context("in GetCompilers::get_compilers()".to_string()))?;
      let output = command.invoke().await?;

      let top_level: serde_yaml::Value = serde_yaml::from_slice(&output.stdout)?;

      static TOP_LEVEL_KEY: Lazy<serde_yaml::Value> =
        Lazy::new(|| serde_yaml::Value::String("compilers".to_string()));
      static SECOND_KEY: Lazy<serde_yaml::Value> =
        Lazy::new(|| serde_yaml::Value::String("compiler".to_string()));

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

  #[cfg(test)]
  mod test {
    use tokio;

    #[tokio::test]
    async fn test_get_compilers() -> Result<(), crate::Error> {
      use crate::{
        commands::{config::*, CommandError},
        SpackInvocation,
      };
      use super_process::{exe, sync::SyncInvocable};

      // Locate all the executables.
      let spack = SpackInvocation::summon().await?;

      // .get_compilers() will return an array of compiler specs.
      let get_compilers = GetCompilers { spack, scope: None };
      let found_compilers = get_compilers
        .clone()
        .get_compilers()
        .await
        .map_err(|e| CommandError::Config(get_compilers.into_base_config(), e))?;
      assert!(!found_compilers.is_empty());

      // Get the path to a working C compiler and check that it can executed.
      let first_cc: exe::Exe = found_compilers[0]
        .paths
        .cc
        .as_ref()
        .expect("cc should have been defined")
        .into();
      let command = exe::Command {
        exe: first_cc,
        argv: ["--version"].into(),
        ..Default::default()
      };
      let output = command
        .invoke()
        .await
        .expect("cc --version should have succeeded");
      assert!(!output.stdout.is_empty());
      Ok(())
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
  use once_cell::sync::Lazy;
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
    pub arch: serde_json::Value,
    pub compiler: serde_json::Value,
    pub namespace: String,
    pub parameters: serde_json::Value,
    pub dependencies: Option<serde_json::Value>,
    /// 32-character hash uniquely identifying this spec: {0}
    pub hash: String,
  }

  impl FoundSpec {
    /// Get a CLI argument matching the exact spec found previously.
    pub fn hashed_spec(&self) -> CLISpec { CLISpec(format!("{}/{}", &self.name, &self.hash)) }
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
    /// output parse error {0}
    Parse(String),
    /// json error {0}
    Json(#[from] serde_json::Error),
  }

  /// Find request.
  #[derive(Debug, Clone)]
  pub struct Find {
    pub spack: SpackInvocation,
    pub spec: CLISpec,
    pub env: Option<EnvName>,
    pub repos: Option<RepoDirs>,
  }

  #[async_trait]
  impl CommandBase for Find {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self {
        spack,
        spec,
        env,
        repos,
      } = self;
      let mut args = exe::Argv(
        ["find", "--json", &spec.0]
          .into_iter()
          .map(|s| OsStr::new(s).to_os_string())
          .collect(),
      );
      if let Some(env) = env {
        env.modify_argv(&mut args);
      }
      if let Some(repos) = repos {
        repos.modify_argv(&mut args);
      }
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
    pub async fn find(self) -> Result<Vec<FoundSpec>, FindError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in Find::find()".to_string()))?;
      let output = command.invoke().await?;

      match serde_json::from_slice::<'_, serde_json::Value>(&output.stdout)? {
        serde_json::Value::Array(values) => {
          let found_specs: Vec<FoundSpec> = values
            .into_iter()
            .map(serde_json::from_value)
            .collect::<Result<Vec<FoundSpec>, _>>()?;
          Ok(found_specs)
        },
        value => Err(FindError::Parse(format!(
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
    pub env: Option<EnvName>,
    pub repos: Option<RepoDirs>,
  }

  #[async_trait]
  impl CommandBase for FindPrefix {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self {
        spack,
        spec,
        env,
        repos,
      } = self;
      let mut args = exe::Argv(
        ["find", "--no-groups", "-p", spec.0.as_ref()]
          .map(|s| OsStr::new(s).to_os_string())
          .into_iter()
          .collect(),
      );

      if let Some(env) = env {
        env.modify_argv(&mut args);
      }
      if let Some(repos) = repos {
        repos.modify_argv(&mut args);
      }

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
    pub async fn find_prefix(self) -> Result<Option<prefix::Prefix>, FindError> {
      let spec = self.spec.clone();
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in FindPrefix::find_prefix()".to_string()))?;

      match command.clone().invoke().await {
        Ok(output) => {
          static FIND_PREFIX_REGEX: Lazy<Regex> =
            Lazy::new(|| Regex::new(r"^([^@]+)@([^ ]+) +([^ ].*)$").unwrap());
          let stdout = str::from_utf8(&output.stdout).map_err(|e| {
            FindError::Parse(format!("failed to parse utf8 ({}): got {:?}", e, &output))
          })?;
          dbg!(&stdout);
          let lines: Vec<&str> = stdout.split('\n').collect();
          let last_line = match lines.iter().filter(|l| !l.is_empty()).last() {
            None => {
              return Err(FindError::Parse(format!(
                "stdout was empty (stderr was {})",
                str::from_utf8(&output.stderr).unwrap_or("<could not parse utf8>"),
              )))
            },
            Some(line) => line,
          };
          dbg!(&last_line);
          let m = FIND_PREFIX_REGEX.captures(last_line).unwrap();
          let name = m.get(1).unwrap().as_str();
          /* FIXME: this method should be using a custom `spack python` script!! */
          assert!(spec.0.starts_with(name));
          let prefix: PathBuf = m.get(3).unwrap().as_str().into();
          Ok(Some(prefix::Prefix { path: prefix }))
        },
        Err(exe::CommandErrorWrapper {
          context,
          error: exe::CommandError::NonZeroExit(1),
          ..
        }) if context.contains("==> No package matches") => Ok(None),
        Err(e) => Err(e.into()),
      }
    }
  }

  #[cfg(test)]
  mod test {
    use tokio;

    #[tokio::test]
    async fn test_find() -> Result<(), crate::Error> {
      use crate::{
        commands::{find::*, install::*},
        SpackInvocation,
      };

      // Locate all the executables.
      let spack = SpackInvocation::summon().await?;

      // Ensure an m4 is installed.
      let install = Install {
        spack: spack.clone(),
        spec: CLISpec::new("m4"),
        verbosity: Default::default(),
        env: None,
        repos: None,
      };
      let found_spec = install.clone().install_find().await.unwrap();

      // Look for an m4 spec with that exact hash.
      let find = Find {
        spack,
        spec: found_spec.hashed_spec(),
        env: None,
        repos: None,
      };

      // .find() will return an array of values, which may have any length.
      let found_specs = find
        .clone()
        .find()
        .await
        .map_err(|e| crate::commands::CommandError::Find(find, e))?;

      // Here, we just check the first of the found specs.
      assert!(&found_specs[0].name == "m4");
      // Verify that this is the same spec as before.
      assert!(&found_specs[0].hash == &found_spec.hash);
      // The fields of the '--json' output of 'find'
      // are deserialized into FoundSpec instances.
      assert!(&found_specs[0].version.0[..4] == "1.4.");
      Ok(())
    }

    #[tokio::test]
    async fn test_find_prefix() -> Result<(), crate::Error> {
      use crate::{
        commands::{find::*, install::*},
        SpackInvocation,
      };
      use std::fs;

      // Locate all the executables.
      let spack = SpackInvocation::summon().await?;

      // Ensure an m4 is installed.
      let install = Install {
        spack: spack.clone(),
        spec: CLISpec::new("m4"),
        verbosity: Default::default(),
        env: None,
        repos: None,
      };
      let found_spec = install
        .clone()
        .install_find()
        .await
        .map_err(|e| crate::commands::CommandError::Install(install, e))?;

      // Look for an m4 spec with that exact hash.
      let find_prefix = FindPrefix {
        spack,
        spec: found_spec.hashed_spec(),
        env: None,
        repos: None,
      };

      // .find_prefix() will return the spec's prefix root wrapped in an Option.
      let m4_prefix = find_prefix
        .clone()
        .find_prefix()
        .await
        .map_err(|e| crate::commands::CommandError::FindPrefix(find_prefix, e))?
        .unwrap();

      // Verify that this prefix contains the m4 executable.
      let m4_exe = m4_prefix.path.join("bin").join("m4");
      assert!(fs::File::open(m4_exe).is_ok());
      Ok(())
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
    pub async fn load(self) -> Result<exe::EnvModifications, LoadError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in Load::load()".to_string()))?;
      let load_output = command.invoke().await?;
      /* dbg!(std::str::from_utf8(&load_output.stdout).unwrap()); */

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

  #[cfg(test)]
  mod test {
    use tokio;

    #[tokio::test]
    async fn test_load() -> Result<(), crate::Error> {
      use crate::{
        commands::{install::*, load::*},
        SpackInvocation,
      };
      use std::ffi::OsStr;
      use super_process::exe;

      // Locate all the executables.
      let spack = SpackInvocation::summon().await?;

      // Ensure an m4 is installed.
      let install = Install {
        spack: spack.clone(),
        spec: CLISpec::new("m4"),
        verbosity: Default::default(),
        env: None,
        repos: None,
      };
      let found_spec = install.clone().install_find().await.unwrap();

      // Look for a m4 spec with that exact hash.
      let load = Load {
        spack,
        specs: vec![found_spec.hashed_spec()],
      };
      let exe::EnvModifications(m4_env) = load
        .clone()
        .load()
        .await
        .map_err(|e| crate::commands::CommandError::Load(load, e))?;
      // This is the contents of a source-able environment script.
      assert!(m4_env.contains_key(OsStr::new("M4")));
      Ok(())
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
  use num_cpus;

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
    fn default() -> Self { Self::Verbose }
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
    pub env: Option<EnvName>,
    pub repos: Option<RepoDirs>,
  }

  #[async_trait]
  impl CommandBase for Install {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self {
        spack,
        spec,
        verbosity,
        env,
        repos,
      } = self;

      /* Generate spack argv. */
      /* FIXME: determine appropriate amount of build parallelism! */
      let jobs_arg = format!("-j{}", num_cpus::get());
      let mut args = vec!["install", "--fail-fast", &jobs_arg];
      /* If running this inside an environment, the command will fail without this
       * argument. */
      if env.is_some() {
        args.push("--add");
      }
      let mut argv = exe::Argv(
        args
          .into_iter()
          .map(|s| s.to_string())
          .chain(verbosity.verbosity_args())
          .chain([spec.0.clone()])
          .map(|s| OsStr::new(&s).to_os_string())
          .collect(),
      );

      if let Some(env) = env {
        env.modify_argv(&mut argv);
      }
      if let Some(repos) = repos {
        repos.modify_argv(&mut argv);
      }

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
    /// Execute `spack install "$self.spec"`, piping stdout and stderr to the
    /// terminal.
    pub async fn install(self) -> Result<(), InstallError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in Install::install()".to_string()))?;

      /* Kick off the child process, reading its streams asynchronously. */
      let streaming = command.invoke_streaming()?;
      streaming.wait().await?;

      Ok(())
    }

    /// Execute [`Self::install`], then execute [`Find::find`].
    pub async fn install_find(self) -> Result<FoundSpec, InstallError> {
      let Self {
        spack,
        spec,
        env,
        repos,
        ..
      } = self.clone();

      /* Check if the spec already exists. */
      let cached_find = Find {
        spack,
        spec,
        env,
        repos,
      };
      /* FIXME: ensure we have a test for both cached and uncached!!! */
      if let Ok(found_specs) = cached_find.clone().find().await {
        return Ok(found_specs[0].clone());
      }

      self.install().await?;

      /* Find the first match for the spec we just tried to install. */
      /* NB: this will probably immediately break if the CLI spec covers more than
       * one concrete spec! For now we just take the first result!! */
      let found_specs = cached_find
        .clone()
        .find()
        .await
        .map_err(|e| CommandError::Find(cached_find, e))
        .map_err(|e| InstallError::Inner(Box::new(e)))?;
      Ok(found_specs[0].clone())
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
        .map_err(|e| e.with_context("in Install::install_with_env()".to_string()))?;
      command.env = load_env;

      let streaming = command.invoke_streaming()?;
      streaming.wait().await?;

      Ok(())
    }
  }

  #[cfg(test)]
  mod test {
    use tokio;

    #[tokio::test]
    async fn test_install() -> Result<(), crate::Error> {
      use crate::{commands::install::*, SpackInvocation};

      // Locate all the executables.
      let spack = SpackInvocation::summon().await?;

      // Install libiberty, if we don't have it already!
      let install = Install {
        spack: spack.clone(),
        spec: CLISpec::new("libiberty@2.37"),
        verbosity: Default::default(),
        env: None,
        repos: None,
      };
      let found_spec = install
        .clone()
        .install_find()
        .await
        .map_err(|e| crate::commands::CommandError::Install(install, e))?;

      // The result matches our query!
      assert!(&found_spec.name == "libiberty");
      assert!(&found_spec.version.0 == "2.37");
      Ok(())
    }

    #[tokio::test]
    async fn test_install_find() -> Result<(), crate::Error> {
      use crate::{commands::install::*, SpackInvocation};

      // Locate all the executables.
      let spack = SpackInvocation::summon().await?;

      // Install libiberty, if we don't have it already!
      let install = Install {
        spack: spack.clone(),
        spec: CLISpec::new("libiberty@2.37"),
        verbosity: Default::default(),
        env: None,
        repos: None,
      };
      let found_spec = install
        .clone()
        .install_find()
        .await
        .map_err(|e| crate::commands::CommandError::Install(install, e))?;

      // The result matches our query!
      assert!(&found_spec.name == "libiberty");
      assert!(&found_spec.version.0 == "2.37");
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
    pub env: Option<EnvName>,
    pub repos: Option<RepoDirs>,
    /// Optional command line to evaluate within the package environment.
    ///
    /// If this argv is empty, the contents of the environment are printed to
    /// stdout with `env`.
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
        env,
        argv,
        dump,
        repos,
      } = self;

      let dump_args = if let Some(d) = dump {
        vec!["--dump".to_string(), format!("{}", d.display())]
      } else {
        vec![]
      };

      let mut argv = exe::Argv(
        ["build-env".to_string()]
          .into_iter()
          .chain(dump_args)
          .chain([spec.0])
          .map(|s| OsStr::new(&s).to_os_string())
          .chain(argv.trailing_args().0)
          .collect(),
      );

      if let Some(env) = env {
        env.modify_argv(&mut argv);
      }
      if let Some(repos) = repos {
        repos.modify_argv(&mut argv);
      }

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
    pub async fn build_env(self) -> Result<sync::RawOutput, BuildEnvError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in BuildEnv::build_env()".to_string()))?;
      let output = command.invoke().await?;
      Ok(output)
    }
  }

  #[cfg(test)]
  mod test {
    use tokio;

    #[tokio::test]
    async fn test_build_env() -> Result<(), crate::Error> {
      let td = tempdir::TempDir::new("spack-summon-test").unwrap();
      use crate::{
        commands::{build_env::*, install::*},
        SpackInvocation,
      };
      use std::{fs, io::BufRead};

      // Locate all the executables.
      let spack = SpackInvocation::summon().await?;

      // Let's get an m4 installed!
      let install = Install {
        spack: spack.clone(),
        spec: CLISpec::new("m4"),
        verbosity: Default::default(),
        env: None,
        repos: None,
      };
      let found_spec = install
        .clone()
        .install_find()
        .await
        .map_err(|e| crate::commands::CommandError::Install(install, e))?;

      // Now let's activate the build environment for it!
      let build_env = BuildEnv {
        spack: spack.clone(),
        // Use the precise spec we just ensured was installed.
        spec: found_spec.hashed_spec(),
        env: None,
        repos: None,
        dump: None,
        argv: Default::default(),
      };
      // Execute build-env to get an env printed to stdout.
      let output = build_env
        .clone()
        .build_env()
        .await
        .map_err(|e| crate::commands::CommandError::BuildEnv(build_env, e))?;

      // Example ad-hoc parsing of environment source files.
      let mut spec_was_found: bool = false;
      for line in output.stdout.lines() {
        let line = line.unwrap();
        if line.starts_with("SPACK_SHORT_SPEC") {
          spec_was_found = true;
          assert!("m4" == &line[17..19]);
        }
      }
      assert!(spec_was_found);

      // Now let's write out the environment to a file using --dump!
      let dump = td.path().join(".env-dump");
      let build_env = BuildEnv {
        spack: spack.clone(),
        spec: found_spec.hashed_spec(),
        env: None,
        repos: None,
        dump: Some(dump.clone()),
        argv: Default::default(),
      };
      // We will have written to ./.env-dump!
      let _ = build_env
        .clone()
        .build_env()
        .await
        .map_err(|e| crate::commands::CommandError::BuildEnv(build_env, e))?;
      spec_was_found = false;
      for line in fs::read_to_string(&dump)
        .expect(".env-dump was created")
        .lines()
      {
        if line.starts_with("SPACK_SHORT_SPEC") {
          spec_was_found = true;
          assert!("m4" == &line[18..20]);
        }
      }
      assert!(spec_was_found);

      // Now let's try running a command line in a build-env!
      let build_env = BuildEnv {
        spack,
        spec: found_spec.hashed_spec(),
        env: None,
        repos: None,
        dump: None,
        argv: ["sh", "-c", "echo $SPACK_SHORT_SPEC"].as_ref().into(),
      };
      let output = build_env
        .clone()
        .build_env()
        .await
        .map_err(|e| crate::commands::CommandError::BuildEnv(build_env, e))?;
      assert!(&output.stdout[..2] == b"m4");
      Ok(())
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
          .chain(passthrough.0)
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

  #[cfg(test)]
  mod test {
    use tokio;

    #[tokio::test]
    async fn test_python() -> Result<(), crate::Error> {
      use crate::{commands::python, SpackInvocation};
      use super_process::{base::CommandBase, sync::SyncInvocable};

      // Locate all the executables.
      let spack = SpackInvocation::summon().await.unwrap();

      // Create python execution request.
      let spack_python = python::SpackPython {
        spack: spack.clone(),
        script: "import spack; print(spack.__version__)".to_string(),
        passthrough: Default::default(),
      };
      let command = spack_python
        .setup_command()
        .await
        .expect("hydration failed");

      // Spawn the child process and wait for it to complete.
      let output = command.clone().invoke().await.expect("sync command failed");
      // Parse output into UTF-8...
      let decoded = output.decode(command.clone()).expect("decoding failed");
      // ...and verify the version matches `spack.version`.
      let version = decoded.stdout.strip_suffix("\n").unwrap();
      assert!(version == &spack.version);
      Ok(())
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
    /// The scope to request the config be written into.
    pub scope: Option<String>,
  }

  #[async_trait]
  impl CommandBase for CompilerFind {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      let Self {
        spack,
        paths,
        scope,
      } = self;
      let args = exe::Argv(
        ["compiler", "find"]
          .map(|s| s.to_string())
          .into_iter()
          .chain(
            scope
              .map(|s| vec!["--scope".to_string(), s])
              .unwrap_or_else(Vec::new),
          )
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
    /// Use [`FindCompilerSpecs::find_compiler_specs`] to get information about
    /// the compilers spack can find.
    pub async fn compiler_find(self) -> Result<(), CompilerFindError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in compiler_find()!".to_string()))?;
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
    /// Run a custom `spack python` script to print out compiler specs located
    /// in the given paths.
    ///
    /// If the given set of [`Self::paths`] is empty, use the defaults from
    /// config.
    pub async fn find_compiler_specs(self) -> Result<Vec<FoundCompiler>, CompilerFindError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in find_compiler_specs()!".to_string()))?;
      let output = command.invoke().await?;

      match serde_json::from_slice::<'_, serde_json::Value>(&output.stdout)? {
        serde_json::Value::Array(values) => {
          let compiler_specs: Vec<FoundCompiler> = values
            .into_iter()
            .map(serde_json::from_value)
            .collect::<Result<Vec<FoundCompiler>, _>>()?;
          Ok(compiler_specs)
        },
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

  #[cfg(test)]
  mod test {
    use tokio;

    #[tokio::test]
    async fn test_compiler_find() -> Result<(), crate::Error> {
      use crate::{commands::compiler_find::*, SpackInvocation};

      // Locate all the executables.
      let spack = SpackInvocation::summon().await.unwrap();

      // Create compiler-find execution request.
      let find_compiler_specs = FindCompilerSpecs {
        spack: spack.clone(),
        paths: vec![],
      };
      let found_compilers = find_compiler_specs
        .clone()
        .find_compiler_specs()
        .await
        .map_err(|e| CommandError::FindCompilerSpecs(find_compiler_specs, e))?;
      // The first compiler on the list is gcc or clang!
      let first_name = &found_compilers[0].compiler.name;
      assert!(first_name.starts_with("gcc") || first_name.starts_with("clang"));
      Ok(())
    }

    #[tokio::test]
    async fn test_find_compiler_specs() -> Result<(), crate::Error> {
      use crate::{commands::compiler_find::*, SpackInvocation};

      // Locate all the executables.
      let spack = SpackInvocation::summon().await.unwrap();

      // Create compiler-find execution request.
      let find_compiler_specs = FindCompilerSpecs {
        spack: spack.clone(),
        paths: vec![],
      };
      let found_compilers = find_compiler_specs
        .clone()
        .find_compiler_specs()
        .await
        .map_err(|e| CommandError::FindCompilerSpecs(find_compiler_specs, e))?;
      // The first compiler on the list is gcc or clang!
      let first_name = &found_compilers[0].compiler.name;
      assert!(first_name.starts_with("gcc") || first_name.starts_with("clang"));
      Ok(())
    }
  }
}

/// `checksum` command.
pub mod checksum {
  use super::*;
  use crate::SpackInvocation;
  use super_process::{
    base::{self, CommandBase},
    exe,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use indexmap::IndexSet;
  use tokio::task;

  use std::{ffi::OsStr, io, path::PathBuf, str};


  #[derive(Debug, Display, Error)]
  pub enum ChecksumError {
    /// command line error {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// setup error {0}
    Setup(#[from] base::SetupErrorWrapper),
    /// utf-8 decoding error {0}
    Utf8(#[from] str::Utf8Error),
    /// io error {0}
    Io(#[from] io::Error),
  }

  #[derive(Debug, Clone)]
  pub struct VersionsRequest {
    #[allow(missing_docs)]
    pub spack: SpackInvocation,
    pub package_name: String,
  }

  #[async_trait]
  impl CommandBase for VersionsRequest {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      eprintln!("VersionsRequest");
      dbg!(&self);
      let Self {
        spack,
        package_name,
      } = self;

      let argv = exe::Argv(
        ["versions", "--safe", &package_name]
          .into_iter()
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

  impl VersionsRequest {
    pub async fn safe_versions(self) -> Result<Vec<String>, ChecksumError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in VersionsRequest::safe_versions()".to_string()))?;
      let output = command.invoke().await?;

      let versions: Vec<String> = str::from_utf8(&output.stdout)?
        .split('\n')
        .filter(|s| !s.is_empty())
        .map(|s| s.strip_prefix("  ").unwrap().to_string())
        .collect();

      Ok(versions)
    }
  }

  /// Request to add a new version to a package in the summoned spack repo.
  #[derive(Debug, Clone)]
  pub struct AddToPackage {
    #[allow(missing_docs)]
    pub spack: SpackInvocation,
    pub package_name: String,
    pub new_version: String,
  }

  #[async_trait]
  impl CommandBase for AddToPackage {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      eprintln!("AddToPackage");
      dbg!(&self);
      let Self {
        spack,
        package_name,
        new_version,
      } = self;

      let argv = exe::Argv(
        ["checksum", "--add-to-package", &package_name, &new_version]
          .into_iter()
          .map(|s| OsStr::new(&s).to_os_string())
          .collect(),
      );

      /* Accept the changes without user interaction. */
      let env: exe::EnvModifications = [("SPACK_EDITOR", "echo")].into();

      Ok(
        spack
          .with_spack_exe(exe::Command {
            argv,
            env,
            ..Default::default()
          })
          .setup_command()
          .await?,
      )
    }
  }

  pub(crate) static ENSURE_PACKAGE_VERSION_LOCK: once_cell::sync::Lazy<tokio::sync::Mutex<()>> =
    once_cell::sync::Lazy::new(|| tokio::sync::Mutex::new(()));

  impl AddToPackage {
    async fn version_is_known(
      req: VersionsRequest,
      new_version: &str,
    ) -> Result<bool, ChecksumError> {
      let versions: IndexSet<String> = req.safe_versions().await?.into_iter().collect();

      Ok(versions.contains(new_version))
    }

    async fn force_new_version(
      self,
      req: VersionsRequest,
      new_version: &str,
    ) -> Result<(), ChecksumError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in add_to_package()!".to_string()))?;

      /* Execute the command. */
      let _ = command.invoke().await?;

      /* Confirm that we have created the target version. */
      assert!(Self::version_is_known(req, new_version).await?);

      Ok(())
    }

    pub async fn idempotent_ensure_version_for_package(self) -> Result<(), ChecksumError> {
      /* Our use of file locking within the summoning process does not
       * differentiate between different threads within the same process, so
       * we additionally lock in-process here. */
      let _lock = ENSURE_PACKAGE_VERSION_LOCK.lock().await;

      let req = VersionsRequest {
        spack: self.spack.clone(),
        package_name: self.package_name.clone(),
      };

      /* If the version is already known, we are done. */
      if Self::version_is_known(req.clone(), &self.new_version).await? {
        eprintln!(
          "we already have the version {} for package {}!",
          &self.new_version, &self.package_name
        );
        return Ok(());
      }

      /* FIXME: in-process mutex too!! generalize this! */
      let lockfile_name: PathBuf =
        format!("{}@{}.lock", &self.package_name, &self.new_version).into();
      let lockfile_path = self.spack.cache_location().join(lockfile_name);
      let mut lockfile = task::spawn_blocking(move || fslock::LockFile::open(&lockfile_path))
        .await
        .unwrap()?;
      /* This unlocks the lockfile upon drop! */
      let _lockfile = task::spawn_blocking(move || {
        lockfile.lock_with_pid()?;
        Ok::<_, io::Error>(lockfile)
      })
      .await
      .unwrap()?;

      /* See if the target version was created since we locked the lockfile. */
      if Self::version_is_known(req.clone(), &self.new_version).await? {
        eprintln!(
          "the version {} for package {} was created while we locked the file handle!",
          &self.new_version, &self.package_name
        );
        return Ok(());
      }

      /* Otherwise, we will execute a command that modifies the summoned checkout. */
      let new_version = self.new_version.clone();
      self.force_new_version(req, &new_version).await?;

      Ok(())
    }
  }

  #[cfg(test)]
  mod test {
    use super::*;

    #[tokio::test]
    async fn test_ensure_re2_2022_12_01() -> eyre::Result<()> {
      // Locate all the executables.
      let spack = SpackInvocation::summon().await?;

      let req = AddToPackage {
        spack,
        package_name: "re2".to_string(),
        new_version: "2022-12-01".to_string(),
      };
      req.idempotent_ensure_version_for_package().await?;

      Ok(())
    }
  }
}

pub mod env {
  use super::*;
  use crate::{metadata_spec::spec, SpackInvocation};
  use super_process::{
    base::{self, CommandBase},
    exe,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use indexmap::IndexSet;
  use tokio::task;

  use std::{borrow::Cow, ffi::OsStr, io, path::PathBuf};

  #[derive(Debug, Display, Error)]
  pub enum EnvError {
    /// install error {0}
    Install(#[from] install::InstallError),
    /// command line error {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// setup error {0}
    Setup(#[from] base::SetupErrorWrapper),
    /// io error {0}
    Io(#[from] io::Error),
  }

  #[derive(Debug, Clone)]
  pub struct EnvList {
    #[allow(missing_docs)]
    pub spack: SpackInvocation,
  }

  #[async_trait]
  impl CommandBase for EnvList {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      eprintln!("EnvList");
      dbg!(&self);
      let Self { spack } = self;

      let argv = exe::Argv(
        ["env", "list"]
          .into_iter()
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

  impl EnvList {
    pub async fn env_list(self) -> Result<IndexSet<EnvName>, EnvError> {
      let command = self
        .setup_command()
        .await
        .map_err(|e| e.with_context("in env_list()!".to_string()))?;
      let output = command.clone().invoke().await?;
      let output = output.decode(command)?;
      Ok(
        output
          .stdout
          .split('\n')
          .map(|s| EnvName(s.trim().to_string()))
          .collect(),
      )
    }
  }

  #[derive(Debug, Clone)]
  pub struct EnvCreate {
    #[allow(missing_docs)]
    pub spack: SpackInvocation,
    pub env: EnvName,
  }

  #[async_trait]
  impl CommandBase for EnvCreate {
    async fn setup_command(self) -> Result<exe::Command, base::SetupError> {
      eprintln!("EnvCreate");
      dbg!(&self);
      let Self {
        spack,
        env: EnvName(env_name),
      } = self;

      let argv = exe::Argv(
        ["env", "create", env_name.as_str()]
          .into_iter()
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

  pub(crate) static ENSURE_ENV_CREATE_LOCK: once_cell::sync::Lazy<tokio::sync::Mutex<()>> =
    once_cell::sync::Lazy::new(|| tokio::sync::Mutex::new(()));

  impl EnvCreate {
    async fn env_exists(env_list: EnvList, env_name: &EnvName) -> Result<bool, EnvError> {
      let existing_envs = env_list.env_list().await?;
      Ok(existing_envs.contains(env_name))
    }

    pub async fn idempotent_env_create(
      self,
      instructions: Cow<'_, spec::EnvInstructions>,
    ) -> Result<EnvName, EnvError> {
      /* Our use of file locking within the summoning process does not
       * differentiate between different threads within the same process, so
       * we additionally lock in-process here. */
      let _lock = ENSURE_ENV_CREATE_LOCK.lock().await;

      let req = EnvList {
        spack: self.spack.clone(),
      };

      let completed_sentinel_filename: PathBuf = format!("SENTINEL@env@{}", &self.env.0).into();
      let sentinel_file = self
        .spack
        .cache_location()
        .join(completed_sentinel_filename);
      dbg!(&sentinel_file);
      if sentinel_file.is_file() {
        assert!(Self::env_exists(req.clone(), &self.env).await?);
        eprintln!(
          "env {:?} already exists and sentinel file {} does too!",
          &self.env,
          sentinel_file.display()
        );
        return Ok(self.env);
      }

      /* FIXME: in-process mutex too!! generalize this! */
      let lockfile_name: PathBuf = format!("env@{}.lock", &self.env.0).into();
      let lockfile_path = self.spack.cache_location().join(lockfile_name);
      dbg!(&lockfile_path);
      let mut lockfile = task::spawn_blocking(move || fslock::LockFile::open(&lockfile_path))
        .await
        .unwrap()?;

      /* This unlocks the lockfile upon drop! */
      let _lockfile = task::spawn_blocking(move || {
        lockfile.lock_with_pid()?;
        Ok::<_, io::Error>(lockfile)
      })
      .await
      .unwrap()?;

      let spack = self.spack.clone();
      let env = self.env.clone();

      if Self::env_exists(req.clone(), &env).await? {
        eprintln!(
          "the env {:?} was created while waiting for file lock!",
          &env
        );
      } else {
        let command = self
          .setup_command()
          .await
          .map_err(|e| e.with_context("in idempotent_env_create()!".to_string()))?;
        let _ = command.invoke().await?;
        assert!(Self::env_exists(req, &env).await?);
      }

      /* While holding the lock, install all the specs in the order given. */
      dbg!(&instructions);
      let spec::EnvInstructions { specs, repo } = instructions.into_owned();
      let repo_dirs = match repo {
        Some(spec::Repo { path }) => Some(RepoDirs(vec![std::env::current_dir()?.join(path)])),
        None => None,
      };

      for spec in specs.into_iter() {
        let spec = CLISpec::new(spec.0);
        let install = install::Install {
          spack: spack.clone(),
          spec,
          verbosity: install::InstallVerbosity::Verbose,
          env: Some(env.clone()),
          repos: repo_dirs.clone(),
        };
        install.install().await?;
      }

      let outfile = sentinel_file.clone();
      task::spawn_blocking(move || std::fs::write(outfile, b""))
        .await
        .unwrap()?;
      assert!(sentinel_file.is_file());

      Ok(env)
    }
  }
}
