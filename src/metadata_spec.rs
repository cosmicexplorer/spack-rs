/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

pub mod spec {
  use base64ct::{Base64Url, Encoding};
  use displaydoc::Display;
  use indexmap::IndexMap;
  use serde::Deserialize;
  use sha3::{Digest, Sha3_256};
  use thiserror::Error;

  use std::str;

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct EnvLabel(pub String);

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Spec(pub String);

  #[derive(Debug, Clone, Deserialize)]
  pub struct Dep {
    pub r#type: String,
    pub lib_names: Vec<String>,
  }

  /// This is deserialized from the output of `cargo metadata --format-version
  /// 1` with [`serde_json`].
  ///
  /// Cargo packages can declare these attributes in their `Cargo.toml` in the
  /// `[package.metadata.spack]` section as follows:
  ///```toml
  /// [package.metadata.spack]
  /// env_label               = "re2-runtime-deps"
  /// spec                    = "re2@2023-11-01~shared ^ abseil-cpp+shared"
  /// deps                    = { re2 = { type = "dynamic", lib_names = ["re2"] } }
  /// ```
  #[derive(Debug, Clone, Deserialize)]
  pub struct LabelledPackageMetadata {
    pub env_label: String,
    pub spec: String,
    pub deps: IndexMap<String, Dep>,
  }

  /// Name of a package from the [`Spec`] resolver.
  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct PackageName(pub String);

  /// Name of a cargo package.
  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct CrateName(pub String);

  #[derive(Debug, Display, Error)]
  pub enum SpecError {
    /// error parsing: {0}
    Parsing(String),
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum LibraryType {
    /// link against this library statically
    Static,
    /// link against this library dynamically, and set -Wl,-rpath
    DynamicWithRpath,
  }

  impl str::FromStr for LibraryType {
    type Err = SpecError;

    fn from_str(s: &str) -> Result<Self, SpecError> {
      match s {
        "static" => Ok(Self::Static),
        "dynamic" => Ok(Self::DynamicWithRpath),
        s => Err(SpecError::Parsing(format!(
          "dep type only accepts \"static\" or \"dynamic\"; was {:?}",
          s
        ))),
      }
    }
  }

  #[derive(Debug, Clone)]
  pub struct SubDep {
    pub pkg_name: PackageName,
    pub r#type: LibraryType,
    pub lib_names: Vec<String>,
  }

  #[derive(Debug, Clone)]
  pub struct Recipe {
    pub env_label: EnvLabel,
    pub sub_deps: Vec<SubDep>,
  }

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct EnvInstructions {
    pub specs: Vec<Spec>,
  }

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  #[repr(transparent)]
  pub struct EnvHash(pub [u8; 32]);

  impl EnvHash {
    fn base64_encoded(&self) -> String { Base64Url::encode_string(&self.0[..]) }

    pub fn hashed_env_name(&self, readable_name: &str) -> String {
      format!(
        "{}-{}",
        readable_name,
        self.base64_encoded().strip_suffix('=').unwrap()
      )
    }
  }

  impl EnvInstructions {
    pub fn compute_digest(&self) -> EnvHash {
      let mut hasher = Sha3_256::new();
      for Spec(s) in self.specs.iter() {
        hasher.update(s);
      }
      EnvHash(hasher.finalize().into())
    }
  }

  #[derive(Debug, Clone)]
  pub struct DisjointResolves {
    pub by_label: IndexMap<EnvLabel, EnvInstructions>,
    pub recipes: IndexMap<CrateName, Recipe>,
  }
}
