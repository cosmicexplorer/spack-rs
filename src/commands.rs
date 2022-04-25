/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

//! Invoking specific spack commands.

use crate::invocation::SpackInvocation;

use displaydoc::Display;
use serde::{Deserialize, Serialize};
use serde_json;
use thiserror::Error;

use std::process;

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
    pub spack: SpackInvocation,
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
    /// let spack = SpackInvocation::create(python, spack_exe).await?;
    /// let install = Install { spack, spec: CLISpec::new("python@3:") };
    /// let found_spec = install.install().await?;
    /// assert!(&found_spec.name == "python");
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
      let _ = spack
        .clone()
        .invoke(&args)
        .await
        .map_err(|e| CommandError::Install(self, InstallError::Inner(Box::new(e))))?;
      let find = Find { spack, spec };
      Ok(
        find
          .clone()
          .find()
          .await
          .map_err(|e| CommandError::Find(find, e))?,
      )
    }
  }
}

/// Find command.
pub mod find {
  use super::*;

  /// A single package's spec from running [Find::find].
  #[derive(Debug, Display, Serialize, Deserialize, Clone)]
  pub struct FoundSpec {
    /// Package name.
    pub name: String,
    version: String,
    arch: serde_json::Value,
    compiler: serde_json::Value,
    namespace: String,
    parameters: serde_json::Value,
    dependencies: Option<serde_json::Value>,
    /// 32-character hash uniquely identifying this spec.
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
    pub spack: SpackInvocation,
    pub spec: CLISpec,
  }

  impl Find {
    /// Execute `spack find "$self.spec"`.
    pub async fn find(self) -> Result<FoundSpec, FindError> {
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
        serde_json::Value::Array(values) if values.len() == 1 => {
          let found_spec: FoundSpec = serde_json::from_value(values[0].clone())
            .map_err(|e| FindError::Serde(format!("{}", values[0].clone()), e))?;
          Ok(found_spec)
        }
        value => Err(FindError::Unknown(format!(
          "unable to parse find output: {:?}",
          value
        ))),
      }
    }
  }
}
