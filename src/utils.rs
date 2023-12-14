/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

use crate::{
  commands::{self, find, install},
  subprocess::spack::SpackInvocation,
};

use std::{fs, io, path::Path};

/// Like [`fs::create_dir_all`], except handles concurrent calls among multiple
/// threads or processes. Originally lifted from rustc, then from pants.
pub fn safe_create_dir_all_ioerror(path: &Path) -> Result<(), io::Error> {
  match fs::create_dir(path) {
    Ok(()) => return Ok(()),
    Err(ref e) if e.kind() == io::ErrorKind::AlreadyExists => return Ok(()),
    Err(ref e) if e.kind() == io::ErrorKind::NotFound => {},
    Err(e) => return Err(e),
  }
  match path.parent() {
    Some(p) => safe_create_dir_all_ioerror(p)?,
    None => return Ok(()),
  }
  match fs::create_dir(path) {
    Ok(()) => Ok(()),
    Err(ref e) if e.kind() == io::ErrorKind::AlreadyExists => Ok(()),
    Err(e) => Err(e),
  }
}

/// Call `spack install <spec>` and parse the result of `spack find --json`.
///
/// The installation via `spack install` will be cached using spack's normal
/// caching mechanisms.
pub async fn ensure_installed(
  spack: SpackInvocation,
  spec: commands::CLISpec,
) -> Result<find::FoundSpec, crate::Error> {
  let install = install::Install {
    spack: spack.clone(),
    spec,
    verbosity: Default::default(),
    env: None,
  };
  let found_spec = install
    .clone()
    .install_find()
    .await
    .map_err(|e| commands::CommandError::Install(install, e))?;
  Ok(found_spec)
}

/// Call [`ensure_installed`], then return its installation root prefix from
/// within `opt/spack/...`.
pub async fn ensure_prefix(
  spack: SpackInvocation,
  spec: commands::CLISpec,
) -> Result<prefix::Prefix, crate::Error> {
  let found_spec = ensure_installed(spack.clone(), spec).await?;
  let find_prefix = find::FindPrefix {
    spack,
    spec: found_spec.hashed_spec(),
    env: None,
  };
  let prefix = find_prefix
    .clone()
    .find_prefix()
    .await
    .map_err(|e| commands::CommandError::FindPrefix(find_prefix, e))?
    .expect("when using a spec with a hash, FindPrefix should never return None");
  Ok(prefix)
}

/// Utilities for building code with [wasm] support via [emscripten].
///
/// [wasm]: https://webassembly.org
/// [emscripten]: https://emscripten.org
pub mod wasm {
  use crate::commands::find;

  const LLVM_FOR_WASM: &str = "llvm@14:\
+lld+clang+multiple-definitions\
~compiler-rt~tools-extra-clang~libcxx~gold~openmp~internal_unwind~polly \
targets=webassembly";

  /// Ensure that a version of llvm is installed that is able to support
  /// emscripten.
  pub async fn ensure_wasm_ready_llvm(
    spack: crate::SpackInvocation,
  ) -> Result<find::FoundSpec, crate::Error> {
    let llvm_found_spec = super::ensure_installed(spack, LLVM_FOR_WASM.into()).await?;
    Ok(llvm_found_spec)
  }
}

#[cfg(test)]
mod test {
  use tokio;

  /* #[tokio::test] */
  /* async fn test_ensure_wasm_ready_llvm() -> Result<(), crate::Error> { */
  /* use crate::{utils, SpackInvocation}; */
  /* use super_process::{exe, fs, sync::SyncInvocable}; */

  /* // Locate all the executables. */
  /* let spack = SpackInvocation::summon().await?; */

  /* // Let's look for an `llvm` installation, and find the `llvm-config`
   * executable. */
  /* let llvm = utils::wasm::ensure_wasm_ready_llvm(spack.clone()).await?; */
  /* let llvm_prefix = utils::ensure_prefix(spack, llvm.hashed_spec()).await?; */
  /* let llvm_config_path = llvm_prefix.path.join("bin").join("llvm-config"); */

  /* // Let's make sure the executable can be executed successfully! */
  /* let command = exe::Command { */
  /* exe: exe::Exe(fs::File(llvm_config_path)), */
  /* argv: ["--targets-built"].as_ref().into(), */
  /* ..Default::default() */
  /* }; */
  /* let output = command */
  /* .invoke() */
  /* .await */
  /* .expect("expected llvm-config command to succeed"); */
  /* let stdout = std::str::from_utf8(&output.stdout).unwrap(); */
  /* assert!(stdout.contains("WebAssembly")); */
  /* Ok(()) */
  /* } */

  #[tokio::test]
  async fn test_ensure_prefix() -> Result<(), crate::Error> {
    use crate::{utils, SpackInvocation};
    use super_process::{exe, fs, sync::SyncInvocable};

    // Locate all the executables.
    let spack = SpackInvocation::summon().await?;

    // Let's look for an `m4` installation, and find the `m4` executable.
    let m4_prefix = utils::ensure_prefix(spack, "m4".into()).await?;
    let m4_bin_path = m4_prefix.path.join("bin").join("m4");

    // Let's make sure the executable can be executed successfully!
    let command = exe::Command {
      exe: exe::Exe(fs::File(m4_bin_path)),
      argv: ["--version"].as_ref().into(),
      ..Default::default()
    };
    let output = command
      .invoke()
      .await
      .expect("expected m4 command to succeed");
    assert!(output.stdout.starts_with(b"m4 "));
    Ok(())
  }

  #[tokio::test]
  async fn test_ensure_installed() -> Result<(), crate::Error> {
    // Locate all the executables.
    let spack = crate::SpackInvocation::summon().await?;

    // Let's look for an `m4` installation.
    let m4_spec = crate::utils::ensure_installed(spack, "m4".into()).await?;
    assert!(&m4_spec.name == "m4");
    Ok(())
  }
}

pub mod prefix {
  use async_stream::try_stream;
  use displaydoc::Display;
  use futures_core::stream::Stream;
  use futures_util::{pin_mut, stream::TryStreamExt};
  use indexmap::{IndexMap, IndexSet};
  use once_cell::sync::Lazy;
  use regex::Regex;
  use thiserror::Error;
  use walkdir;

  use std::path::{Path, PathBuf};

  #[derive(Debug, Display, Error)]
  pub enum PrefixTraversalError {
    /// walkdir error: {0}
    Walkdir(#[from] walkdir::Error),
    /// needed libs {0:?} not found at prefix {1:?}: found libs were {2:?}
    NeededLibrariesNotFound(IndexSet<LibraryName>, Prefix, IndexSet<LibraryName>),
    /// duplicated libs {0:?} found at multiple paths from prefix {1:?}:\n{2:?}
    DuplicateLibraryNames(
      IndexSet<LibraryName>,
      Prefix,
      IndexMap<LibraryName, Vec<CABILibrary>>,
    ),
  }

  /// {0}
  #[derive(Debug, Display, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
  pub struct LibraryName(pub String);

  #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
  pub enum LibraryType {
    Static,
    #[default]
    Dynamic,
  }

  impl LibraryType {
    pub(crate) fn cargo_lib_type(&self) -> &'static str {
      match self {
        Self::Static => "static",
        Self::Dynamic => "dylib",
      }
    }

    pub(crate) fn match_filename_suffix(suffix: &str) -> Option<Self> {
      match suffix {
        "a" => Some(Self::Static),
        "so" => Some(Self::Dynamic),
        _ => None,
      }
    }
  }

  #[derive(Debug, Clone)]
  pub struct CABILibrary {
    pub name: LibraryName,
    pub path: PathBuf,
    pub kind: LibraryType,
  }

  impl CABILibrary {
    pub fn containing_directory(&self) -> &Path {
      self
        .path
        .parent()
        .expect("library path should have a parent directory!")
    }

    pub fn minus_l_arg(&self) -> String { format!("{}={}", self.kind.cargo_lib_type(), self.name) }

    pub fn parse_file_path(file_path: &Path) -> Option<Self> {
      static LIBNAME_PATTERN: Lazy<Regex> =
        Lazy::new(|| Regex::new(r"^lib([^/]+)\.(a|so)$").unwrap());
      let filename = match file_path.file_name() {
        Some(component) => component.to_string_lossy(),
        /* All files have a name, and we only care about files, so ignore directories like '..'
         * which don't have a name. */
        None => {
          return None;
        },
      };
      if let Some(m) = LIBNAME_PATTERN.captures(&filename) {
        let name = LibraryName(m.get(1).unwrap().as_str().to_string());
        let kind = LibraryType::match_filename_suffix(m.get(2).unwrap().as_str())
          .expect("validated that only .a or .so files can match LIBNAME_PATTERN regex");
        Some(Self {
          path: file_path.to_path_buf(),
          name,
          kind,
        })
      } else {
        None
      }
    }
  }

  #[derive(Debug, Clone)]
  pub struct Prefix {
    pub path: PathBuf,
  }

  impl Prefix {
    pub fn traverse(&self) -> impl Stream<Item=Result<walkdir::DirEntry, walkdir::Error>> {
      let path = self.path.clone();
      try_stream! {
        for file in walkdir::WalkDir::new(path) {
          yield file?;
        }
      }
    }
  }

  #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
  pub enum SearchBehavior {
    #[default]
    ErrorOnDuplicateLibraryName,
    SelectFirstForEachLibraryName,
  }

  #[derive(Debug, Clone, Default)]
  pub struct LibsQuery {
    pub needed_libraries: Vec<LibraryName>,
    pub kind: LibraryType,
    pub search_behavior: SearchBehavior,
  }

  impl LibsQuery {
    pub async fn find_libs(self, prefix: &Prefix) -> Result<LibCollection, PrefixTraversalError> {
      let Self {
        needed_libraries,
        kind,
        search_behavior,
      } = self;
      let needed_libraries: IndexSet<LibraryName> = needed_libraries.iter().cloned().collect();
      let mut libs_by_name: IndexMap<LibraryName, Vec<CABILibrary>> = IndexMap::new();

      let s = prefix.traverse();
      pin_mut!(s);

      while let Some(dir_entry) = s.try_next().await? {
        let lib_path = dir_entry.into_path();
        match CABILibrary::parse_file_path(&lib_path) {
          Some(lib) if lib.kind == kind => {
            dbg!(&lib);
            libs_by_name
              .entry(lib.name.clone())
              .or_insert_with(Vec::new)
              .push(lib);
          },
          _ => (),
        }
      }

      let found: IndexSet<LibraryName> = libs_by_name.keys().cloned().collect();
      let needed_not_found: IndexSet<LibraryName> =
        needed_libraries.difference(&found).cloned().collect();
      if !needed_not_found.is_empty() {
        return Err(PrefixTraversalError::NeededLibrariesNotFound(
          needed_not_found,
          prefix.clone(),
          found,
        ));
      }
      let only_needed_libs: IndexMap<LibraryName, Vec<CABILibrary>> = libs_by_name
        .into_iter()
        .filter(|(name, _)| needed_libraries.contains(name))
        .collect();

      let mut singly_matched_libs: IndexMap<LibraryName, CABILibrary> = IndexMap::new();
      let mut duplicated_libs: IndexMap<LibraryName, Vec<CABILibrary>> = IndexMap::new();
      for (name, mut libs) in only_needed_libs.into_iter() {
        assert!(!libs.is_empty());
        if libs.len() == 1 {
          singly_matched_libs.insert(name, libs.pop().unwrap());
        } else {
          duplicated_libs.insert(name, libs);
        }
      }

      match search_behavior {
        SearchBehavior::ErrorOnDuplicateLibraryName => {
          if !duplicated_libs.is_empty() {
            return Err(PrefixTraversalError::DuplicateLibraryNames(
              duplicated_libs.keys().cloned().collect(),
              prefix.clone(),
              duplicated_libs,
            ));
          }
        },
        SearchBehavior::SelectFirstForEachLibraryName => {
          for (name, libs) in duplicated_libs.into_iter() {
            assert!(!singly_matched_libs.contains_key(&name));
            assert!(!libs.is_empty());
            dbg!(&name);
            dbg!(&libs);
            singly_matched_libs.insert(name, libs.into_iter().next().unwrap());
          }
        },
      }
      assert_eq!(singly_matched_libs.len(), needed_libraries.len());

      Ok(LibCollection {
        found_libraries: singly_matched_libs.into_values().collect(),
      })
    }
  }

  #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, Default)]
  pub enum RpathBehavior {
    #[default]
    DoNotSetRpath,
    SetRpathForContainingDirs,
  }

  #[derive(Debug, Clone)]
  pub struct LibCollection {
    pub found_libraries: Vec<CABILibrary>,
  }

  impl LibCollection {
    pub fn link_libraries(self, rpath_behavior: RpathBehavior) {
      let mut containing_dirs: IndexSet<PathBuf> = IndexSet::new();
      for lib in self.found_libraries.into_iter() {
        println!("cargo:rerun-if-changed={}", lib.path.display());
        println!("cargo:rustc-link-lib={}", lib.minus_l_arg());
        containing_dirs.insert(lib.containing_directory().to_path_buf());

        if rpath_behavior == RpathBehavior::SetRpathForContainingDirs {
          assert_eq!(lib.kind, LibraryType::Dynamic);
        }
      }

      for dir in containing_dirs.iter() {
        println!("cargo:rustc-link-search=native={}", dir.display());
      }

      if rpath_behavior == RpathBehavior::SetRpathForContainingDirs {
        for dir in containing_dirs.iter() {
          println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir.display());
        }
        let joined_rpath: String = containing_dirs
          .into_iter()
          .map(|p| format!("{}", p.display()))
          .collect::<Vec<_>>()
          .join(":");
        println!("cargo:joined_rpath={}", joined_rpath);
      }
    }
  }
}

pub mod metadata {
  use crate::metadata_spec::spec;
  use super_process::{exe, sync::SyncInvocable};

  use displaydoc::Display;
  use guppy::CargoMetadata;
  use indexmap::{IndexMap, IndexSet};
  use serde_json;
  use thiserror::Error;

  use std::{env, io};

  #[derive(Debug, Display, Error)]
  pub enum MetadataError {
    /// error processing specs {0}
    Spec(#[from] spec::SpecError),
    /// command line error {0}
    Command(#[from] exe::CommandErrorWrapper),
    /// io error {0}
    Io(#[from] io::Error),
    /// json error {0}
    Json(#[from] serde_json::Error),
    /// guppy error {0}
    Guppy(#[from] guppy::Error),
  }

  pub async fn get_metadata() -> Result<spec::DisjointResolves, MetadataError> {
    let cargo_exe: exe::Exe = env::var("CARGO").as_ref().unwrap().into();
    let cargo_argv: exe::Argv = ["metadata", "--format-version", "1"].into();
    let cargo_cmd = exe::Command {
      exe: cargo_exe,
      argv: cargo_argv,
      ..Default::default()
    };

    let metadata =
      CargoMetadata::parse_json(cargo_cmd.clone().invoke().await?.decode(cargo_cmd)?.stdout)?;
    let package_graph = metadata.build_graph()?;

    let labelled_metadata: Vec<(
      spec::CrateName,
      spec::LabelledPackageMetadata,
      Vec<spec::CargoFeature>,
    )> = package_graph
      .packages()
      .filter_map(|p| {
        let name = spec::CrateName(p.name().to_string());
        let spack_metadata = p.metadata_table().as_object()?.get("spack")?.clone();
        dbg!(&spack_metadata);
        let features: Vec<_> = p
          .named_features()
          .map(|s| spec::CargoFeature(s.to_string()))
          .collect();
        Some((name, spack_metadata, features))
      })
      .map(|(name, spack_metadata, features)| {
        let spec_metadata: spec::LabelledPackageMetadata = serde_json::from_value(spack_metadata)?;
        Ok((name, spec_metadata, features))
      })
      .collect::<Result<Vec<_>, MetadataError>>()?;

    let mut resolves: IndexMap<spec::Label, Vec<spec::Spec>> = IndexMap::new();
    let mut recipes: IndexMap<
      spec::CrateName,
      IndexMap<spec::Label, (spec::Recipe, spec::FeatureMap)>,
    > = IndexMap::new();
    let mut declared_features_by_package: IndexMap<spec::CrateName, Vec<spec::CargoFeature>> =
      IndexMap::new();

    for (crate_name, spec::LabelledPackageMetadata { envs }, features) in
      labelled_metadata.into_iter()
    {
      dbg!(&envs);

      assert!(declared_features_by_package
        .insert(crate_name.clone(), features)
        .is_none());

      for (label, env) in envs.into_iter() {
        let spec::Env {
          spec,
          deps,
          features,
        } = env;
        let env_label = spec::Label(label);
        let spec = spec::Spec(spec);
        let feature_map = if let Some(spec::FeatureLayout {
          needed,
          conflicting,
        }) = features
        {
          let needed: IndexSet<_> = needed
            .unwrap_or_default()
            .into_iter()
            .map(spec::CargoFeature)
            .collect();
          let conflicting: IndexSet<_> = conflicting
            .unwrap_or_default()
            .into_iter()
            .map(spec::CargoFeature)
            .collect();
          spec::FeatureMap {
            needed,
            conflicting,
          }
        } else {
          spec::FeatureMap::default()
        };

        let sub_deps: Vec<spec::SubDep> = deps
          .into_iter()
          .map(|(pkg_name, spec::Dep { r#type, lib_names })| {
            Ok(spec::SubDep {
              pkg_name: spec::PackageName(pkg_name),
              r#type: r#type.parse()?,
              lib_names,
            })
          })
          .collect::<Result<Vec<_>, spec::SpecError>>()?;

        let recipe = spec::Recipe { sub_deps };

        resolves.entry(env_label.clone()).or_default().push(spec);
        assert!(recipes
          .entry(crate_name.clone())
          .or_default()
          .insert(env_label, (recipe, feature_map))
          .is_none());
      }
    }

    Ok(spec::DisjointResolves {
      by_label: resolves
        .into_iter()
        .map(|(label, specs)| (label, spec::EnvInstructions { specs }))
        .collect(),
      recipes,
      declared_features_by_package,
    })
  }

  pub fn get_cur_pkg_name() -> spec::CrateName {
    spec::CrateName(env::var("CARGO_PKG_NAME").unwrap())
  }
}

/// High-level API for build scripts that consumes `[package.metadata.spack]`.
pub mod declarative {
  pub mod resolve {
    use crate::{
      commands::*,
      metadata_spec::spec,
      subprocess::spack::SpackInvocation,
      utils::{declarative::linker, metadata, prefix},
    };

    use std::borrow::Cow;

    use indexmap::IndexMap;

    fn currently_has_feature(feature: &spec::CargoFeature) -> bool {
      std::env::var(feature.to_env_var_name()).is_ok()
    }

    async fn resolve_recipe(
      env_label: spec::Label,
      recipe: &spec::Recipe,
      env_instructions: &spec::EnvInstructions,
    ) -> eyre::Result<Vec<prefix::Prefix>> {
      let env_hash = env_instructions.compute_digest();
      let env = EnvName(env_hash.hashed_env_name(&env_label.0));
      dbg!(&env);

      /* Ensure spack is available. */
      let spack = SpackInvocation::summon().await?;

      /* Create the environment and install all specs into it if not already
       * created. */
      let env = env::EnvCreate {
        spack: spack.clone(),
        env,
      }
      .idempotent_env_create(Cow::Borrowed(env_instructions))
      .await?;

      let mut dep_prefixes: Vec<prefix::Prefix> = Vec::new();

      /* Process each resolved dependency to hook it up into cargo. */
      for sub_dep in recipe.sub_deps.iter() {
        let env = env.clone();
        let spack = spack.clone();
        let req = find::FindPrefix {
          spack: spack.clone(),
          spec: CLISpec::new(&sub_dep.pkg_name.0),
          env: Some(env.clone()),
        };
        let prefix = req.find_prefix().await?.unwrap();

        linker::link_against_dependency(
          prefix.clone(),
          sub_dep.r#type,
          sub_dep.lib_names.iter().map(|s| s.as_str()),
        )
        .await?;
        dep_prefixes.push(prefix);
      }

      Ok(dep_prefixes)
    }

    pub async fn resolve_dependencies_for_label(
      env_label: spec::Label,
    ) -> eyre::Result<Vec<prefix::Prefix>> {
      println!("cargo:rerun-if-changed=Cargo.toml");

      /* Parse `cargo metadata` for the entire workspace. */
      let metadata = metadata::get_metadata().await?;
      /* Get the current package name. */
      let cur_pkg_name = metadata::get_cur_pkg_name();

      /* Get the current package's recipe with the given label. */
      let declared_recipes: &IndexMap<spec::Label, (spec::Recipe, spec::FeatureMap)> =
        metadata.recipes.get(&cur_pkg_name).unwrap();
      dbg!(declared_recipes);
      let specified_recipe: &spec::Recipe = declared_recipes
        .get(&env_label)
        .map(|(recipe, _)| recipe)
        .ok_or_else(|| {
          eyre::Report::msg(format!(
            "unable to find label {:?} in declarations {:?}",
            &env_label, declared_recipes,
          ))
        })?;

      let env_instructions = metadata.by_label.get(&env_label).unwrap();
      dbg!(env_instructions);

      resolve_recipe(env_label, specified_recipe, env_instructions).await
    }

    pub async fn resolve_dependencies() -> eyre::Result<Vec<prefix::Prefix>> {
      println!("cargo:rerun-if-changed=Cargo.toml");

      /* Parse `cargo metadata` for the entire workspace. */
      let metadata = metadata::get_metadata().await?;
      /* Get the current package name. */
      let cur_pkg_name = metadata::get_cur_pkg_name();

      /* Get the current package's recipes. */
      let declared_recipes: &IndexMap<spec::Label, (spec::Recipe, spec::FeatureMap)> =
        metadata.recipes.get(&cur_pkg_name).unwrap();
      dbg!(&declared_recipes);

      /* Get the declared features for the current package. */
      let declared_features = metadata
        .declared_features_by_package
        .get(&cur_pkg_name)
        .unwrap();
      let activated_features = spec::FeatureSet(
        declared_features
          .iter()
          .filter(|f| currently_has_feature(f))
          .cloned()
          .collect(),
      );

      /* Get the recipe matching the current set of activated features. */
      let matching_recipes: Vec<(&spec::Label, &spec::Recipe)> = declared_recipes
        .into_iter()
        .filter(|(_, (_, feature_map))| feature_map.evaluate(&activated_features))
        .map(|(label, (recipe, _))| (label, recipe))
        .collect();

      let (env_label, cur_recipe) = match matching_recipes.len() {
        0 => {
          return Err(eyre::Report::msg(format!(
            "no recipe found for given features {:?} from declared recipes {:?}",
            activated_features, declared_recipes,
          )))
        },
        1 => matching_recipes[0],
        _ => {
          return Err(eyre::Report::msg(format!(
            "more than one recipe {:?} matched for given features {:?} from declared recipes {:?}",
            matching_recipes, activated_features, declared_recipes,
          )))
        },
      };
      dbg!(&env_label);
      dbg!(&cur_recipe);

      /* Get a hashed name for the current environment to resolve. */
      let env_instructions = metadata.by_label.get(env_label).unwrap();
      dbg!(env_instructions);

      resolve_recipe(env_label.clone(), cur_recipe, env_instructions).await
    }
  }

  pub mod bindings {
    use crate::utils::prefix;

    use std::path::PathBuf;

    pub fn get_include_subdir(prefix: prefix::Prefix) -> PathBuf { prefix.path.join("include") }
  }

  pub mod linker {
    use crate::{metadata_spec::spec, utils::prefix};

    pub async fn link_against_dependency(
      prefix: prefix::Prefix,
      r#type: spec::LibraryType,
      lib_names: impl Iterator<Item=&str>,
    ) -> eyre::Result<()> {
      let needed_libraries: Vec<_> = lib_names
        .map(|s| prefix::LibraryName(s.to_string()))
        .collect();
      let kind = match r#type {
        spec::LibraryType::Static => prefix::LibraryType::Static,
        spec::LibraryType::DynamicWithRpath => prefix::LibraryType::Dynamic,
      };
      let query = prefix::LibsQuery {
        needed_libraries,
        kind,
        search_behavior: prefix::SearchBehavior::ErrorOnDuplicateLibraryName,
      };
      let libs = query.find_libs(&prefix).await?;

      let rpath_behavior = match kind {
        /* No rpath necessary for static linking. */
        prefix::LibraryType::Static => prefix::RpathBehavior::DoNotSetRpath,
        prefix::LibraryType::Dynamic => prefix::RpathBehavior::SetRpathForContainingDirs,
      };
      libs.link_libraries(rpath_behavior);

      Ok(())
    }
  }
}
