/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

pub mod spec {
  use displaydoc::Display;
  use indexmap::{IndexMap, IndexSet};
  use serde::Deserialize;
  use thiserror::Error;

  use std::path::PathBuf;

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct EnvLabel(pub String);

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Spec(pub String);

  /// This is deserialized from the output of `cargo metadata --format-version
  /// 1` with [`serde_json`].
  ///
  /// Cargo packages can declare these attributes in their `Cargo.toml` in the
  /// `[package.metadata.spack]` section as follows:
  ///```toml
  /// [package.metadata.spack]
  /// env_label               = "re2-runtime-deps"
  /// spec                    = "re2@2023-11-01~shared ^ abseil-cpp+shared"
  /// static_libs             = ["re2"]
  /// shared_libs             = ["abseil-cpp"]
  /// cxx                     = "c++17"
  /// bindings_allowlist      = ["absl::*", "re2::.*"]
  /// header_path             = "src/re2.hpp"
  /// bindings_output_path    = "src/bindings.rs"
  /// ```
  #[derive(Debug, Clone, Deserialize)]
  pub struct LabelledPackageMetadata {
    pub env_label: String,
    pub spec: String,
    pub static_libs: Vec<String>,
    pub shared_libs: Vec<String>,
    pub cxx: Option<String>,
    pub bindings_allowlist: Vec<String>,
    pub header_path: PathBuf,
    pub bindings_output_path: PathBuf,
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

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum CxxSupport {
    None,
    Std17,
  }

  impl CxxSupport {
    pub fn parse(s: Option<&str>) -> Result<Self, SpecError> {
      match s {
        None => Ok(Self::None),
        Some(s) => {
          if s == "c++17" {
            Ok(Self::Std17)
          } else {
            Err(SpecError::Parsing(format!(
              "cxx only supports the value \"c++17\"; was {:?}",
              s
            )))
          }
        },
      }
    }
  }

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Recipe {
    pub env_label: EnvLabel,
    pub static_libs: Vec<PackageName>,
    pub shared_libs: Vec<PackageName>,
    pub cxx: CxxSupport,
    pub bindings_allowlist: Vec<String>,
    pub header_path: PathBuf,
    pub bindings_output_path: PathBuf,
  }

  #[derive(Debug, Clone)]
  pub struct DisjointResolves {
    pub by_label: IndexMap<EnvLabel, Vec<Spec>>,
    pub recipes: IndexMap<CrateName, Recipe>,
  }
}

pub mod cache {
  use super::spec;

  use std::path::PathBuf;

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct ConcreteSpec(pub String);

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct ConcreteResolve {
    pub env_label: spec::EnvLabel,
    pub concrete_spec: ConcreteSpec,
  }
}
