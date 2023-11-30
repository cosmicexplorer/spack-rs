/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

pub mod spec {
  use base64ct::{Base64Url, Encoding};
  use displaydoc::Display;
  use indexmap::IndexMap;
  use serde::Deserialize;
  use sha3::{Digest, Sha3_256};
  use thiserror::Error;

  use std::path::PathBuf;

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct EnvLabel(pub String);

  #[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub struct Spec(pub String);

  #[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
  pub struct BindgenConfig {
    pub process_comments: bool,
    pub header_path: PathBuf,
    pub output_path: PathBuf,
  }

  #[derive(Debug, Clone, Deserialize)]
  pub struct Dep {
    pub r#type: String,
    pub lib_names: Vec<String>,
    pub allowlist: Vec<String>,
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
  /// cxx                     = "c++17"
  /// ```
  #[derive(Debug, Clone, Deserialize)]
  pub struct LabelledPackageMetadata {
    pub env_label: String,
    pub spec: String,
    pub cxx: Option<String>,
    pub bindgen: BindgenConfig,
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
    Static,
    DynamicWithRpath,
  }

  impl LibraryType {
    pub fn parse(s: &str) -> Result<Self, SpecError> {
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

  #[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
  pub enum CxxSupport {
    None,
    Std14,
    Std17,
    Std20,
  }

  impl CxxSupport {
    pub fn parse(s: Option<&str>) -> Result<Self, SpecError> {
      match s {
        None => Ok(Self::None),
        Some(s) => {
          if s == "c++17" {
            Ok(Self::Std17)
          } else if s == "c++14" {
            Ok(Self::Std14)
          } else if s == "c++20" {
            Ok(Self::Std20)
          } else {
            Err(SpecError::Parsing(format!(
              "cxx only supports \"c++20\" or \"c++17\" or \"c++14\"; was {:?}",
              s
            )))
          }
        },
      }
    }
  }

  #[derive(Debug, Clone)]
  pub struct SubDep {
    pub pkg_name: PackageName,
    pub r#type: LibraryType,
    pub lib_names: Vec<String>,
    pub allowlist: Vec<String>,
  }

  #[derive(Debug, Clone)]
  pub struct Recipe {
    pub env_label: EnvLabel,
    pub cxx: CxxSupport,
    pub sub_deps: Vec<SubDep>,
    pub bindgen_config: BindgenConfig,
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
      let strs: Vec<&str> = self.specs.iter().map(|Spec(s)| s.as_str()).collect();
      let combined_output: String = strs[..].join("\n");
      hasher.update(combined_output.as_bytes());
      EnvHash(hasher.finalize().into())
    }
  }

  #[derive(Debug, Clone)]
  pub struct DisjointResolves {
    pub by_label: IndexMap<EnvLabel, EnvInstructions>,
    pub recipes: IndexMap<CrateName, Recipe>,
  }
}
