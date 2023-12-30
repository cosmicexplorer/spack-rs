/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

pub mod spec {
  use base64ct::{Base64Url, Encoding};
  use displaydoc::Display;
  use indexmap::{IndexMap, IndexSet};
  use serde::Deserialize;
  use sha3::{Digest, Sha3_256};
  use thiserror::Error;

  use std::{path::PathBuf, str};

  #[derive(Debug, Clone, Deserialize)]
  pub struct Dep {
    pub r#type: String,
    pub lib_names: Vec<String>,
  }

  #[derive(Debug, Clone, Deserialize)]
  pub struct FeatureLayout {
    pub needed: Option<IndexSet<String>>,
    pub conflicting: Option<IndexSet<String>>,
  }

  #[derive(Debug, Clone, Deserialize)]
  pub struct Env {
    pub spec: String,
    pub deps: IndexMap<String, Dep>,
    pub features: Option<FeatureLayout>,
  }

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize)]
  pub struct Repo {
    pub path: PathBuf,
  }

  /// This is deserialized from the output of `cargo metadata --format-version
  /// 1` with [`serde_json`].
  ///
  /// Cargo packages can declare these attributes in their `Cargo.toml` in the
  /// `[package.metadata.spack]` section as follows:
  ///```toml
  /// [package.metadata.spack]
  /// envs = [{
  ///   label = "re2",
  ///   spec = "re2@2023-11-01+shared",
  ///   deps = { re2 = { type = "dynamic", lib_names = ["re2"] } }
  /// }]
  /// ```
  #[derive(Debug, Clone, Deserialize)]
  pub struct LabelledPackageMetadata {
    pub envs: IndexMap<String, Env>,
    pub repo: Option<Repo>,
  }

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Label(pub String);

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Spec(pub String);

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
    pub sub_deps: Vec<SubDep>,
  }

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct EnvInstructions {
    pub specs: Vec<Spec>,
    pub repo: Option<Repo>,
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
      if let Some(ref repo) = self.repo {
        hasher.update(repo.path.as_os_str().as_encoded_bytes());
      }
      EnvHash(hasher.finalize().into())
    }
  }

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct CargoFeature(pub String);

  impl CargoFeature {
    /// This [environment variable] will be set in the current package's build
    /// script if the feature is activated.
    ///
    /// [environment variable]: https://doc.rust-lang.org/cargo/reference/environment-variables.html.
    pub fn to_env_var_name(&self) -> String {
      format!("CARGO_FEATURE_{}", self.0.to_uppercase().replace('-', "_"))
    }
  }

  #[derive(Debug, Clone, Default)]
  pub struct FeatureMap {
    pub needed: IndexSet<CargoFeature>,
    pub conflicting: IndexSet<CargoFeature>,
  }

  impl FeatureMap {
    pub fn evaluate(&self, features: &FeatureSet) -> bool {
      let Self {
        needed,
        conflicting,
      } = self;
      for n in needed.iter() {
        if !features.0.contains(n) {
          return false;
        }
      }
      for c in conflicting.iter() {
        if features.0.contains(c) {
          return false;
        }
      }
      true
    }
  }

  #[derive(Debug, Clone, Default)]
  pub struct FeatureSet(pub IndexSet<CargoFeature>);

  #[derive(Debug, Clone)]
  pub struct DisjointResolves {
    pub by_label: IndexMap<Label, EnvInstructions>,
    pub recipes: IndexMap<CrateName, IndexMap<Label, (Recipe, FeatureMap)>>,
    pub declared_features_by_package: IndexMap<CrateName, Vec<CargoFeature>>,
  }
}
