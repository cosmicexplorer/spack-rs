/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

use crate::SpackInvocation;
use super_process::{
  base::{self, CommandBase},
  exe,
  sync::SyncInvocable,
};

use indexmap::{IndexMap, IndexSet};
use serde::Deserialize;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EnvLabel(pub String);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Spec(pub String);

/// This is deserialized from the output of `cargo metadata --format-version 1`
/// with [`serde_json`].
///
/// Cargo packages can declare these attributes in their `Cargo.toml` in the
/// `[package.metadata.spack]` section as follows:
///```toml
/// [package.metadata.spack]
/// env_label               = "re2-runtime-deps"
/// spec                    = "re2@2023-11-01~shared ^ abseil-cpp+shared"
/// static_libs             = ["re2"]
/// shared_libs             = ["abseil-cpp"]
///```
#[derive(Debug, Clone, Deserialize)]
pub struct LabelledPackageMetadata {
  pub env_label: String,
  pub spec: String,
  pub static_libs: Vec<String>,
  pub shared_libs: Vec<String>,
}

/// Name of a package from the [`Spec`] resolver.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageName(pub String);

/// Name of a cargo package.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CrateName(pub String);

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PackageMetadata {
  pub crate_name: CrateName,
  pub spec: Spec,
  pub static_libs: Vec<PackageName>,
  pub shared_libs: Vec<PackageName>,
}

#[derive(Debug, Clone)]
pub struct DisjointResolves {
  pub by_label: IndexMap<EnvLabel, Vec<PackageMetadata>>,
  pub crate_name_to_label: IndexMap<CrateName, EnvLabel>,
}
