/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

#![deny(unsafe_code)]
// Turn all warnings into errors!
// #![deny(warnings)]
// Warn for missing docs in general, and hard require crate-level docs.
// #![warn(missing_docs)]
#![warn(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
/* Enable all clippy lints except for many of the pedantic ones. It's a shame this needs to be
 * copied and pasted across crates, but there doesn't appear to be a way to include inner
 * attributes from a common source. */
#![deny(
  clippy::all,
  clippy::default_trait_access,
  clippy::expl_impl_clone_on_copy,
  clippy::if_not_else,
  clippy::needless_continue,
  clippy::unseparated_literal_suffix,
  clippy::used_underscore_binding
)]
/* We use inner modules in several places in this crate for ergonomics. */
#![allow(clippy::module_inception)]
/* It is often more clear to show that nothing is being moved. */
#![allow(clippy::match_ref_pats)]
/* Subjective style. */
#![allow(
  clippy::len_without_is_empty,
  clippy::redundant_field_names,
  clippy::too_many_arguments,
  clippy::single_component_path_imports
)]
/* Default isn't as big a deal as people seem to think it is. */
#![allow(clippy::new_without_default, clippy::new_ret_no_self)]
/* Arc<Mutex> can be more clear than needing to grok Orderings: */
#![allow(clippy::mutex_atomic)]

use bindgen;
use eyre::{Report, WrapErr};
use futures_util::{pin_mut, stream::TryStreamExt};
use spack::{
  self,
  utils::{self, prefix},
  SpackInvocation,
};
use tokio::{fs, task};

use std::{ffi::OsStr, io, path::PathBuf};

async fn link_libraries(prefix: prefix::Prefix) -> eyre::Result<()> {
  let query = prefix::LibsQuery {
    needed_libraries: vec![prefix::LibraryName("re2".to_string())],
    kind: prefix::LibraryType::Static,
    search_behavior: prefix::SearchBehavior::ErrorOnDuplicateLibraryName,
  };
  let libs = query.find_libs(&prefix).await?;

  libs.link_libraries();

  Ok(())
}

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

  libs.link_libraries();

  Ok(())
}

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
        match fs::File::open(&inc_file_path).await {
          Ok(_) => {
            let _ = algorithm_header_path.insert(inc_file_path);
          },
          Err(_) => (),
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
        match fs::File::open(&inc_file_path).await {
          Ok(_) => {
            let _ = basic_string_header_path.insert(inc_file_path);
          },
          Err(_) => (),
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
        match fs::File::open(&inc_file_path).await {
          Ok(_) => {
            let _ = cppconfig_header_path.insert(inc_file_path);
          },
          Err(_) => (),
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

async fn generate_bindings(
  re2_prefix: PathBuf,
  header_path: PathBuf,
  output_path: PathBuf,
) -> eyre::Result<()> {
  let re2_header_root = re2_prefix.join("include");

  let bindings = bindgen::Builder::default()
    /* FIXME: is there really not a more specific method than "clang_arg()" to add an include
     * search dir??? */
    .clang_arg(format!("-I{}", re2_header_root.display()))
    .header(format!("{}", header_path.display()))
    .parse_callbacks(Box::new(bindgen::CargoCallbacks::new()))
    .enable_cxx_namespaces()
    .allowlist_item(".*RE2.*");

  /* Pull in the c++ stdlib include dirs. */
  let mut bindings = bindings
    .clang_arg("-std=c++17")
    .clang_args(&["-x", "c++"])
    .opaque_type("std::.*");
  for incdir in locate_cxx_stdlib_system_includes().await?.into_iter() {
    let incdir_str: String = format!("{}", incdir.display());
    dbg!(&incdir_str);
    /* FIXME: why is this necessary??? */
    bindings = bindings.clang_args(&["-cxx-isystem".to_string(), incdir_str]);
  }

  /* FIXME: put within spawn_blocking??? bindings apparently contain non-Send
   * Rc refs (????) */
  let bindings = bindings.generate().unwrap();
  bindings.write_to_file(output_path)?;

  Ok(())
}

#[tokio::main]
async fn main() -> eyre::Result<()> {
  let spack = SpackInvocation::summon().await?;

  let re2_prefix = utils::ensure_prefix(spack, "re2".into()).await?;

  link_libraries(re2_prefix.clone()).await?;

  explicitly_link_cxx_stdlib().await?;

  let header_path = PathBuf::from("src/re2.hpp");
  let bindings_path = PathBuf::from("src/bindings.rs");
  generate_bindings(re2_prefix.path, header_path, bindings_path).await?;

  Ok(())
}
