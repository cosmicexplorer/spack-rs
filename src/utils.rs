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
  use futures_util::{pin_mut, stream::StreamExt};
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
    /// needed libraries {0:?} were not found at prefix {1:?}: found library
    /// names were {2:?}
    NeededLibrariesNotFound(IndexSet<LibraryName>, Prefix, IndexSet<LibraryName>),
    /// duplicated libraries {0:?} were found at multiple paths from prefix
    /// {1:?}:\n{2:?}
    DuplicateLibraryNames(
      IndexSet<LibraryName>,
      Prefix,
      IndexMap<LibraryName, Vec<CABILibrary>>,
    ),
  }

  /// {0}
  #[derive(Debug, Display, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
  pub struct LibraryName(pub String);

  #[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
  pub enum LibraryType {
    Static,
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

  #[derive(Debug, Clone)]
  pub struct LibsQuery {
    pub needed_libraries: Vec<LibraryName>,
    pub kind: LibraryType,
  }

  impl LibsQuery {
    pub async fn find_libs(self, prefix: &Prefix) -> Result<LibCollection, PrefixTraversalError> {
      let Self {
        needed_libraries,
        kind,
      } = self;
      let needed_libraries: IndexSet<_> = needed_libraries.iter().cloned().collect();
      let mut libs_by_name: IndexMap<LibraryName, Vec<CABILibrary>> = IndexMap::new();

      let s = prefix.traverse();
      pin_mut!(s);

      while let Some(dir_entry) = s.next().await {
        let lib_path = dir_entry?.into_path();
        match CABILibrary::parse_file_path(&lib_path) {
          Some(lib) if lib.kind == kind => {
            libs_by_name
              .entry(lib.name.clone())
              .or_insert_with(Vec::new)
              .push(lib);
          },
          _ => (),
        }
      }

      let found: IndexSet<_> = libs_by_name.keys().cloned().collect();
      let needed_not_found: IndexSet<_> = needed_libraries.difference(&found).cloned().collect();
      if !needed_not_found.is_empty() {
        return Err(PrefixTraversalError::NeededLibrariesNotFound(
          needed_not_found,
          prefix.clone(),
          found,
        ));
      }
      let only_needed_libs: IndexMap<_, _> = libs_by_name
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
      if !duplicated_libs.is_empty() {
        return Err(PrefixTraversalError::DuplicateLibraryNames(
          duplicated_libs.keys().cloned().collect(),
          prefix.clone(),
          duplicated_libs,
        ));
      }
      assert_eq!(singly_matched_libs.len(), needed_libraries.len());

      Ok(LibCollection {
        found_libraries: singly_matched_libs.into_values().collect(),
      })
    }
  }

  #[derive(Debug, Clone)]
  pub struct LibCollection {
    pub found_libraries: Vec<CABILibrary>,
  }

  impl LibCollection {
    pub fn link_libraries(self) {
      for lib in self.found_libraries.iter() {
        println!("cargo:rerun-if-changed={}", lib.path.display());
        println!("cargo:rustc-link-lib={}", lib.minus_l_arg());
        println!(
          "cargo:rustc-link-search=native={}",
          lib.containing_directory().display()
        );
      }
    }
  }
}
