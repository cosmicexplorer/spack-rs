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
  use lazy_static::lazy_static;
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
      lazy_static! {
        static ref LIBNAME_PATTERN: Regex = Regex::new(r"^lib([^/]+)\.(a|so)$").unwrap();
      }
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
        println!(
          "cargo:rustc-link-search=native={}",
          lib.containing_directory().display()
        );
        containing_dirs.insert(lib.containing_directory().to_path_buf());

        if rpath_behavior == RpathBehavior::SetRpathForContainingDirs {
          assert_eq!(lib.kind, LibraryType::Dynamic);
        }
      }

      if rpath_behavior == RpathBehavior::SetRpathForContainingDirs {
        for dir in containing_dirs.into_iter() {
          println!("cargo:rustc-link-arg=-Wl,-rpath,{}", dir.display());
        }
      }
    }
  }
}

pub mod metadata {
  use super::*;
  use crate::{metadata_spec::spec, SpackInvocation};
  use super_process::{
    base::{self, CommandBase},
    exe,
    sync::SyncInvocable,
  };

  use async_trait::async_trait;
  use displaydoc::Display;
  use indexmap::{IndexMap, IndexSet};
  use serde_json;
  use thiserror::Error;
  use tokio::task;

  use std::{env, ffi::OsStr, io, path::PathBuf, str};

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
  }

  pub async fn get_metadata() -> Result<spec::DisjointResolves, MetadataError> {
    let cargo_exe: exe::Exe = env::var("CARGO").as_ref().unwrap().into();
    let cargo_argv: exe::Argv = ["metadata", "--format-version", "1"].into();
    let cargo_cmd = exe::Command {
      exe: cargo_exe,
      argv: cargo_argv,
      ..Default::default()
    };
    let decoded_output = cargo_cmd.clone().invoke().await?.decode(cargo_cmd).await?;

    let top_level: serde_json::Map<String, serde_json::Value> =
      task::spawn_blocking(move || serde_json::from_str(&decoded_output.stdout))
        .await
        .unwrap()?;

    let labelled_metadata: Vec<(spec::CrateName, spec::LabelledPackageMetadata)> = top_level
      .get("packages")
      .and_then(|p| p.as_array())
      .unwrap()
      .into_iter()
      .filter_map(|p| p.as_object())
      .filter_map(|p| {
        let spack_metadata: serde_json::Value = p
          .get("metadata")
          .filter(|m| !m.is_null())?
          .as_object()?
          .get("spack")?
          .clone();
        let spack_metadata: spec::LabelledPackageMetadata = serde_json::from_value(spack_metadata)
          .expect("failed to deserialize spack metadata from cargo");
        let name: String = p.get("name")?.as_str()?.to_string();

        Some((spec::CrateName(name), spack_metadata))
      })
      .collect();

    let mut resolves: IndexMap<spec::EnvLabel, Vec<spec::Spec>> = IndexMap::new();
    let mut recipes: IndexMap<spec::CrateName, spec::Recipe> = IndexMap::new();

    for (crate_name, metadata) in labelled_metadata.into_iter() {
      dbg!(&metadata);
      let spec::LabelledPackageMetadata {
        env_label,
        spec,
        cxx,
        bindgen,
        deps,
      } = metadata;
      let env_label = spec::EnvLabel(env_label);
      let spec = spec::Spec(spec);
      let cxx = spec::CxxSupport::parse(cxx.as_ref().map(|x| x.as_str()))?;

      let sub_deps: Vec<spec::SubDep> = {
        let mut deps: Vec<(String, spec::Dep)> = deps.into_iter().collect();
        /* NB: Sort dependencies by name to avoid nondeterministic iteration of
         * HashMap, which is necessary to deserialize the format from json with
         * serde. */
        deps.sort_by_cached_key(|(pkg_name, _)| pkg_name.clone());
        deps
          .into_iter()
          .map(|(pkg_name, dep)| {
            let pkg_name = spec::PackageName(pkg_name);
            let spec::Dep {
              r#type,
              lib_names,
              allowlist,
            } = dep;
            let r#type = spec::LibraryType::parse(&r#type)?;
            Ok(spec::SubDep {
              pkg_name,
              r#type,
              lib_names,
              allowlist,
            })
          })
          .collect::<Result<Vec<_>, spec::SpecError>>()?
      };

      let recipe = spec::Recipe {
        env_label: env_label.clone(),
        cxx,
        sub_deps,
        bindgen_config: bindgen,
      };

      assert!(recipes.insert(crate_name.clone(), recipe).is_none());

      resolves
        .entry(env_label)
        .or_insert_with(Vec::new)
        .push(spec);
    }

    Ok(spec::DisjointResolves {
      by_label: resolves
        .into_iter()
        .map(|(label, specs)| (label, spec::EnvInstructions { specs }))
        .collect(),
      recipes,
    })
  }

  pub fn get_cur_pkg_name() -> spec::CrateName {
    let cur_pkg: String = env::var("CARGO_PKG_NAME").unwrap().into();
    spec::CrateName(cur_pkg)
  }
}

/// High-level API for build scripts that consumes `[package.metadata.spack]`.
pub mod declarative {
  pub async fn resolve_dependencies() -> eyre::Result<()> {
    use crate::{
      commands::*,
      metadata_spec::spec,
      subprocess::spack::SpackInvocation,
      utils::{self, metadata, prefix},
    };

    use indexmap::IndexMap;

    use std::borrow::Cow;

    /* Parse `cargo metadata` for the entire workspace. */
    let metadata = metadata::get_metadata().await?;
    /* Get the current package's recipe. */
    let cur_pkg_name = metadata::get_cur_pkg_name();
    let cur_recipe = metadata.recipes.get(&cur_pkg_name).unwrap();

    /* Get a hashed name for the current environment to resolve. */
    let env_instructions = Cow::Borrowed(metadata.by_label.get(&cur_recipe.env_label).unwrap());
    let env_hash = env_instructions.compute_digest();
    let env = EnvName(env_hash.hashed_env_name(&cur_recipe.env_label.0));

    /* Ensure spack is available. */
    let spack = SpackInvocation::summon().await?;

    /* Create the environment and install all specs into it if not already
     * created. */
    let env = env::EnvCreate {
      spack: spack.clone(),
      env,
    }
    .idempotent_env_create(env_instructions)
    .await?;

    let bindings = bindgen::Builder::default();
    let mut bindings = cxx::enable_hacky_bindgen_cpp_support(bindings, cur_recipe.cxx).await?;
    /* cxx::enable_hacky_linker_cpp_support(cur_recipe.cxx).await?; */
    /* Process each resolved dependency to hook it up into cargo. */
    for sub_dep in cur_recipe.sub_deps.iter() {
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
      bindings = bindings::include_dependency_headers(
        prefix,
        sub_dep.allowlist.iter().map(|s| s.as_str()),
        bindings,
      );
    }
    /* FIXME: If any of the dependencies require a different version of c++, add
     * a dynamic dependency on the C++ stdlib again. THIS SHOULD NOT BE
     * NECESSARY (?) */
    cxx::enable_hacky_linker_cpp_support(cur_recipe.cxx).await?;

    /* FIXME: put within spawn_blocking??? bindings apparently contain non-Send
     * Rc refs (????) */
    bindings
      .header(format!(
        "{}",
        cur_recipe.bindgen_config.header_path.display()
      ))
      .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
      .generate()?
      .write_to_file(&cur_recipe.bindgen_config.output_path)?;

    Ok(())
  }

  pub mod bindings {
    use crate::utils::prefix;

    pub fn include_dependency_headers<'a>(
      prefix: prefix::Prefix,
      allowlist: impl Iterator<Item=&'a str>,
      bindings: bindgen::Builder,
    ) -> bindgen::Builder {
      /* FIXME: is there really not a more specific method than "clang_arg()"
       * to add an include search dir??? */
      let mut bindings = bindings.clang_arg(format!("-I{}/include", prefix.path.display()));
      for item in allowlist {
        bindings = bindings.allowlist_item(item);
      }
      bindings
    }
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

  pub mod cxx {
    use crate::{metadata_spec::spec, utils::prefix};

    use futures_util::{pin_mut, stream::TryStreamExt};
    use tokio::fs;

    use std::{ffi::OsStr, path::PathBuf};

    async fn locate_stl_includes() -> eyre::Result<Vec<PathBuf>> {
      let incstdcpp_prefix = prefix::Prefix {
        path: PathBuf::from("/usr/include/c++"),
      };
      let s = incstdcpp_prefix.traverse();
      pin_mut!(s);

      let mut algorithm_header_path: Option<PathBuf> = None;
      let mut basic_string_header_path: Option<PathBuf> = None;

      while let Some(dir_entry) = s.try_next().await? {
        if algorithm_header_path.is_some() && basic_string_header_path.is_some() {
          break;
        }

        let inc_file_path = dir_entry.into_path();

        if algorithm_header_path.is_none() {
          if inc_file_path
            .file_name()
            .map(|s| s == OsStr::new("algorithm"))
            .unwrap_or(false)
          {
            if inc_file_path.ends_with("parallel/algorithm")
              || inc_file_path.ends_with("experimental/algorithm")
              || inc_file_path.ends_with("ext/algorithm")
            {
              continue;
            }
            if fs::File::open(&inc_file_path).await.is_ok() {
              let _ = algorithm_header_path.insert(inc_file_path);
            }
            continue;
          }
        }

        if basic_string_header_path.is_none() {
          if inc_file_path
            .file_name()
            .map(|s| s == OsStr::new("basic_string.h"))
            .unwrap_or(false)
          {
            assert!(inc_file_path.ends_with("bits/basic_string.h"));
            if fs::File::open(&inc_file_path).await.is_ok() {
              let _ = basic_string_header_path.insert(inc_file_path);
            }
            continue;
          }
        }
      }

      let algorithm_inc_dir = algorithm_header_path
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();
      let basic_string_inc_dir = basic_string_header_path
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();

      Ok(vec![algorithm_inc_dir, basic_string_inc_dir])
    }

    async fn locate_plat_includes() -> eyre::Result<Vec<PathBuf>> {
      let plat_inc_prefix = prefix::Prefix {
        path: PathBuf::from("/usr/include"),
      };
      let s = plat_inc_prefix.traverse();
      pin_mut!(s);

      let mut cppconfig_header_path: Option<PathBuf> = None;

      while let Some(dir_entry) = s.try_next().await? {
        if cppconfig_header_path.is_some() {
          break;
        }

        let inc_file_path = dir_entry.into_path();

        if cppconfig_header_path.is_none() {
          if inc_file_path
            .file_name()
            .map(|s| s == OsStr::new("c++config.h"))
            .unwrap_or(false)
          {
            assert!(inc_file_path.ends_with("bits/c++config.h"));
            if fs::File::open(&inc_file_path).await.is_ok() {
              let _ = cppconfig_header_path.insert(inc_file_path);
            }
            continue;
          }
        }
      }

      let cppconfig_inc_dir = cppconfig_header_path
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .to_path_buf();

      Ok(vec![cppconfig_inc_dir])
    }

    async fn locate_cxx_stdlib_system_includes() -> eyre::Result<Vec<PathBuf>> {
      let mut all_includes = Vec::new();
      all_includes.extend(locate_stl_includes().await?.into_iter());
      all_includes.extend(locate_plat_includes().await?.into_iter());
      Ok(all_includes)
    }

    pub async fn enable_hacky_bindgen_cpp_support(
      bindings: bindgen::Builder,
      cxx: spec::CxxSupport,
    ) -> eyre::Result<bindgen::Builder> {
      dbg!(&cxx);
      let std_arg: &'static str = match cxx {
        // If no C++ support needed, exit early.
        spec::CxxSupport::None => return Ok(bindings),
        spec::CxxSupport::Std17 => "-std=c++17",
        spec::CxxSupport::Std14 => "-std=c++14",
      };
      let mut bindings = bindings
        .clang_arg(std_arg)
        .clang_args(&["-x", "c++"])
        .enable_cxx_namespaces()
        .opaque_type("std::.*");

      /* Pull in the c++ stdlib include dirs. */
      for sys_incdir in locate_cxx_stdlib_system_includes().await?.into_iter() {
        let incdir_str: String = format!("{}", sys_incdir.display());
        dbg!(&incdir_str);
        /* FIXME: why is this necessary??? */
        bindings = bindings.clang_args(&["-cxx-isystem", &incdir_str]);
      }

      Ok(bindings)
    }

    /* FIXME: why is this necessary??? */
    async fn explicitly_link_cxx_stdlib() -> eyre::Result<()> {
      let libstdcpp_prefix = prefix::Prefix {
        path: PathBuf::from("/usr/lib"),
      };
      let query = prefix::LibsQuery {
        needed_libraries: vec![prefix::LibraryName("stdc++".to_string())],
        kind: prefix::LibraryType::Dynamic,
        search_behavior: prefix::SearchBehavior::SelectFirstForEachLibraryName,
      };
      let libs = query.find_libs(&libstdcpp_prefix).await?;

      /* Do not set rpath and rely on the dynamic linker to resolve the C++ stdlib. */
      libs.link_libraries(prefix::RpathBehavior::DoNotSetRpath);

      Ok(())
    }

    pub async fn enable_hacky_linker_cpp_support(cxx: spec::CxxSupport) -> eyre::Result<()> {
      match cxx {
        spec::CxxSupport::None => Ok(()),
        spec::CxxSupport::Std17 | spec::CxxSupport::Std14 => explicitly_link_cxx_stdlib().await,
      }
    }
  }
}
