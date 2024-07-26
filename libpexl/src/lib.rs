/* Copyright 2024 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! ???

// Warn for missing docs in general, and hard require crate-level docs.
/* #![warn(missing_docs)] */
#![deny(rustdoc::missing_crate_level_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]

use displaydoc::Display;
use thiserror::Error;

use std::{ffi, mem::MaybeUninit, ops, ptr};

pub(crate) use libpexl_sys as pexl;

#[derive(Debug, Display, Error)]
pub enum RefError {
  /// ref was invalid
  Invalid,
  /// ref not found
  NotFound,
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Context(*mut pexl::pexl_Context);

impl Context {
  pub fn new() -> Self { Self(unsafe { pexl::pexl_new_Context() }) }

  pub fn bind(&mut self, exp: Option<&mut Expr>, name: Option<&Name>) -> Result<Ref, RefError> {
    Ref::bind(self, exp, name)
  }

  pub fn bind_in(
    &mut self,
    env: Env,
    exp: Option<&mut Expr>,
    name: Option<&Name>,
  ) -> Result<Ref, RefError> {
    Ref::bind_in(self, env, exp, name)
  }

  pub fn match_bytes(&mut self, bytes: &[u8]) -> Expr { Expr::match_bytes(self, bytes) }

  pub fn scope_push(&mut self) -> Env { Env::scope_push(self) }

  pub fn scope_pop(&mut self) -> Env { Env::scope_pop(self) }

  pub fn compile(
    &mut self,
    main: Ref,
    optims: &mut Optims,
    enc: CharEncoding,
  ) -> Result<Binary, PexlError> {
    Binary::compile(self, main, optims, enc)
  }
}

impl ops::Drop for Context {
  fn drop(&mut self) {
    unsafe {
      pexl::pexl_free_Context(self.0);
    }
  }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Name(ffi::CString);

impl Name {
  pub fn from_str(s: &str) -> Result<Self, ffi::NulError> { Ok(Self(ffi::CString::new(s)?)) }

  fn as_ptr(&self) -> *const ffi::c_char { self.0.as_c_str().as_ptr() }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Env(pexl::pexl_Env);

impl Env {
  pub const TOPLEVEL: Self = Self(0);

  pub(crate) fn scope_push(ctx: &mut Context) -> Self {
    Self(unsafe { pexl::pexl_scope_push(ctx.0) })
  }

  pub(crate) fn scope_pop(ctx: &mut Context) -> Self {
    Self(unsafe { pexl::pexl_scope_pop(ctx.0) })
  }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Ref(pexl::pexl_Ref);

impl Ref {
  fn validate(&self) -> Result<(), RefError> {
    if unsafe { pexl::pexl_Ref_invalid(self.0) } {
      return Err(RefError::Invalid);
    }
    if unsafe { pexl::pexl_Ref_notfound(self.0) } {
      return Err(RefError::NotFound);
    }
    Ok(())
  }

  pub(crate) fn bind(
    ctx: &mut Context,
    exp: Option<&mut Expr>,
    name: Option<&Name>,
  ) -> Result<Self, RefError> {
    let ret = Self(unsafe {
      pexl::pexl_bind(
        ctx.0,
        exp.map(|exp| exp.0).unwrap_or_else(ptr::null_mut),
        name.map(|name| name.as_ptr()).unwrap_or_else(ptr::null),
      )
    });
    ret.validate()?;
    Ok(ret)
  }

  pub(crate) fn bind_in(
    ctx: &mut Context,
    env: Env,
    exp: Option<&mut Expr>,
    name: Option<&Name>,
  ) -> Result<Self, RefError> {
    let ret = Self(unsafe {
      pexl::pexl_bind_in(
        ctx.0,
        env.0,
        exp.map(|exp| exp.0).unwrap_or_else(ptr::null_mut),
        name.map(|name| name.as_ptr()).unwrap_or_else(ptr::null),
      )
    });
    ret.validate()?;
    Ok(ret)
  }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Expr(*mut pexl::pexl_Expr);

impl Expr {
  pub(crate) fn match_bytes(ctx: &mut Context, bytes: &[u8]) -> Self {
    Self(unsafe { pexl::pexl_match_bytes(ctx.0, bytes.as_ptr().cast(), bytes.len()) })
  }
}

impl Clone for Expr {
  fn clone(&self) -> Self { Self(unsafe { pexl::pexl_copy_Expr(self.0) }) }
}

impl ops::Drop for Expr {
  fn drop(&mut self) {
    unsafe {
      pexl::pexl_free_Expr(self.0);
    }
  }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Optims(*mut pexl::pexl_Optims);

impl Default for Optims {
  fn default() -> Self { Self(unsafe { pexl::pexl_default_Optims() }) }
}

impl ops::Drop for Optims {
  fn drop(&mut self) { unsafe { pexl::pexl_free_Optims(self.0) } }
}

#[derive(Debug, Display, Copy, Clone, num_enum::IntoPrimitive, num_enum::TryFromPrimitive)]
#[repr(u32)]
pub enum CharEncoding {
  /// ASCII
  Ascii = pexl::pexl_CharEncoding_PEXL_CHAR_ASCII,
  /// UTF-8
  Utf8 = pexl::pexl_CharEncoding_PEXL_CHAR_UTF8,
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Index(pexl::pexl_Index);

impl Index {
  pub(crate) const OK: Self = Self(pexl::PEXL_OK as pexl::pexl_Index);

  pub const fn is_ok(self) -> bool { self.0 == Self::OK.0 }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
#[repr(transparent)]
pub struct PexlError(pexl::pexl_Error);

impl PexlError {
  pub fn is_ok(self) -> bool { self.value().is_ok() }

  pub fn value(self) -> Index { Index(unsafe { pexl::pexl_Error_value(self.0) }) }

  pub fn location(self) -> Index { Index(unsafe { pexl::pexl_Error_location(self.0) }) }
}

#[derive(
  Debug,
  Copy,
  Clone,
  PartialEq,
  Eq,
  PartialOrd,
  Ord,
  Hash,
  num_enum::IntoPrimitive,
  num_enum::TryFromPrimitive,
)]
#[repr(u32)]
pub enum EncoderID {
  NoEncoder = pexl::pexlEncoderID_PEXL_NO_ENCODER,
  DebugEncoder = pexl::pexlEncoderID_PEXL_DEBUG_ENCODER,
  TreeEncoder = pexl::pexlEncoderID_PEXL_TREE_ENCODER,
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Match(*mut pexl::pexl_Match);

impl Match {
  pub fn new(encoder_id: EncoderID) -> Self {
    Self(unsafe { pexl::pexl_new_Match(encoder_id.into()) })
  }

  pub fn failed(&mut self) -> bool { unsafe { pexl::pexl_Match_failed(self.0) } }

  pub fn print(&mut self) {
    unsafe {
      pexl::pexl_print_Match(self.0);
    }
  }

  pub fn print_summary(&mut self) {
    unsafe {
      pexl::pexl_print_Match_summary(self.0);
    }
  }

  pub fn print_data(&mut self) {
    unsafe {
      pexl::pexl_print_Match_data(self.0);
    }
  }
}

impl ops::Drop for Match {
  fn drop(&mut self) {
    unsafe {
      pexl::pexl_free_Match(self.0);
    }
  }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct Binary(*mut pexl::pexl_Binary);

impl Binary {
  pub(crate) fn compile(
    ctx: &mut Context,
    main: Ref,
    optims: &mut Optims,
    enc: CharEncoding,
  ) -> Result<Self, PexlError> {
    let mut err: MaybeUninit<pexl::pexl_Error> = MaybeUninit::uninit();
    let p = unsafe {
      pexl::pexl_compile(
        ctx.0,
        main.0,
        optims.0,
        ptr::null_mut(),
        enc.into(),
        err.as_mut_ptr(),
      )
    };
    let err = PexlError(unsafe { err.assume_init() });
    if !err.is_ok() {
      return Err(err);
    }
    assert!(!p.is_null());
    Ok(Self(p))
  }

  pub fn print(&mut self) {
    unsafe {
      pexl::pexl_print_Binary(self.0);
    }
  }

  pub fn run(
    &mut self,
    patname: &Name,
    input: &[u8],
    start: usize,
    match_: &mut Match,
  ) -> Result<(), ()> {
    if unsafe {
      pexl::pexl_run(
        self.0,
        ptr::null_mut(),
        patname.as_ptr(),
        input.as_ptr().cast(),
        input.len(),
        start,
        0,
        ptr::null_mut(),
        match_.0,
      )
    } == 0
    {
      Ok(())
    } else {
      Err(())
    }
  }
}

impl ops::Drop for Binary {
  fn drop(&mut self) {
    unsafe {
      pexl::pexl_free_Binary(self.0);
    }
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[test]
  fn match_bytes() {
    let mut ctx = Context::new();
    let mut expr = ctx.match_bytes(b"asdf".as_ref());
    let name = Name::from_str("A").unwrap();

    let main = ctx
      .bind_in(Env::TOPLEVEL, Some(&mut expr), Some(&name))
      .unwrap();
    let mut opt = Optims::default();
    let mut bin = ctx.compile(main, &mut opt, CharEncoding::Ascii).unwrap();
    bin.print();

    let mut m1 = Match::new(EncoderID::TreeEncoder);
    bin.run(&name, b"asdf".as_ref(), 0, &mut m1).unwrap();
    assert!(!m1.failed());
    m1.print();
    m1.print_summary();
    m1.print_data();

    let mut m2 = Match::new(EncoderID::TreeEncoder);
    bin.run(&name, b"asd".as_ref(), 0, &mut m2).unwrap();
    assert!(m2.failed());
    m2.print();
    m2.print_summary();
    m2.print_data();
  }
}
