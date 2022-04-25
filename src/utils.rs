/* Copyright 2022 Danny McClanahan */
/* SPDX-License-Identifier: (Apache-2.0 OR MIT) */

use std::{fs, io, path::Path};

///
/// Like [std::fs::create_dir_all], except handles concurrent calls among multiple
/// threads or processes. Originally lifted from rustc, then from pants.
///
pub fn safe_create_dir_all_ioerror(path: &Path) -> Result<(), io::Error> {
  match fs::create_dir(path) {
    Ok(()) => return Ok(()),
    Err(ref e) if e.kind() == io::ErrorKind::AlreadyExists => return Ok(()),
    Err(ref e) if e.kind() == io::ErrorKind::NotFound => {}
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
