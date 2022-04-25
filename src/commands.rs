/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking specific spack commands.

use crate::invocation::{Invocation, InvocationError, StdioLine, Streaming};

use displaydoc::Display;
use futures_lite::{io::BufReader, prelude::*};
use serde::{Deserialize, Serialize};
use serde_json;
use thiserror::Error;

use std::{io, process};

/// A spec string for a command-line argument.
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
    /// let python = Python::detect().await?;
    /// let spack_exe = SpackRepo::summon().await?;
    /// let spack = Invocation::create(python, spack_exe).await?;
    /// let install = Install { spack, spec: CLISpec::new("python@3:") };
    /// let found_spec = install.install().await?;
    /// assert!(&found_spec.name == "python");
    /// assert!(&found_spec.version.0[..2] == "3.");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn install(self) -> Result<FoundSpec, CommandError> {
      let Self { spack, spec } = self.clone();
      let args: Vec<&str> = [
        "install",
        "--verbose",
        "--fail-fast",
        /* FIXME: determine appropriate amount of build parallelism! */
        "-j16",
      ]
      .into_iter()
      .chain([spec.0.as_ref()].into_iter())
      .collect();
      let Streaming {
        child,
        stdout,
        stderr,
      } = spack
        .clone()
        .invoke_streaming(&args)
        .map_err(|e| CommandError::Install(self.clone(), InstallError::Inner(Box::new(e))))?;
      /* stdout wrapping. */
      let mut out_lines = BufReader::new(stdout).lines();
      /* stderr wrapping. */
      let mut err_lines = BufReader::new(stderr).lines();

      /* Crossing the streams!!! */
      while let Some(line) =
        StdioLine::merge_streams(out_lines.next().boxed(), err_lines.next().boxed())
          .await
          .map_err(|e| {
            CommandError::Install(self.clone(), InstallError::Inner(Box::new(e.into())))
          })?
      {
        match line {
          StdioLine::Err(err) => {
            eprintln!("{}", err);
          }
          StdioLine::Out(out) => {
            println!("{}", out);
          }
        }
      }

      /* Ensure process exits successfully. */
      child
        .output()
        .await
        .map_err(|e: io::Error| InstallError::Inner(Box::new(e.into())))
        .and_then(|output| {
          Invocation::analyze_exit_status(&output.status).map_err(|e: InvocationError| {
            InstallError::Inner(Box::new(crate::Error::Invocation(spack.clone(), output, e)))
          })
        })
        .map_err(|e: InstallError| CommandError::Install(self, e))?;

      /* Find the first match for the spec we just tried to install. */
      /* NB: this will probably immediately break if the CLI spec covers more than one concrete
       * spec! For now we just take the first result!! */
      let find = Find { spack, spec };
      let found_specs = find
        .clone()
        .find()
        .await
        .map_err(|e| CommandError::Find(find, e))?;
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

  /// A single package's spec from running [Find::find].
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
    /// use spack::{commands::{*, find::*}, invocation::*, summoning::*};
    /// let python = Python::detect().await?;
    /// let spack_exe = SpackRepo::summon().await?;
    /// let spack = Invocation::create(python, spack_exe).await?;
    /// let find = Find { spack, spec: CLISpec::new("python@3:") };
    /// let found_specs = find.clone().find().await.map_err(|e| CommandError::Find(find, e))?;
    /// assert!(&found_specs[0].name == "python");
    /// assert!(&found_specs[0].version.0[..2] == "3.");
    /// # Ok(())
    /// # }) // async
    /// # }
    ///```
    pub async fn find(self) -> Result<Vec<FoundSpec>, FindError> {
      let Self { spack, spec } = self;
      let args: Vec<&str> = ["find", "--json"]
        .into_iter()
        .chain([spec.0.as_ref()].into_iter())
        .collect();
      let process::Output { stdout, .. } = spack
        .invoke(&args)
        .await
        .map_err(|e| FindError::Inner(Box::new(e)))?;
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
