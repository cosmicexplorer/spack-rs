/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#[cfg(feature = "compile")]
use crate::{
  error::HyperscanCompileError,
  expression::{Expression, ExpressionSet, Literal, LiteralSet},
  flags::{CpuFeatures, Flags, Mode, TuneFamily},
};
use crate::{error::HyperscanRuntimeError, hs, state::Scratch};

#[cfg(feature = "compile")]
use once_cell::sync::Lazy;

#[cfg(feature = "compile")]
use std::ptr;
use std::{
  borrow::Cow,
  ffi::CStr,
  mem::{self, MaybeUninit},
  ops,
  os::raw::c_char,
  slice, str,
};

#[derive(Debug)]
#[repr(transparent)]
pub struct Database(*mut NativeDb);

pub type NativeDb = hs::hs_database;

impl Database {
  pub const unsafe fn from_native(p: *mut NativeDb) -> Self { Self(p) }

  pub fn as_ref_native(&self) -> &NativeDb { unsafe { &*self.0 } }

  pub fn as_mut_native(&mut self) -> &mut NativeDb { unsafe { &mut *self.0 } }

  pub fn allocate_scratch(&self) -> Result<Scratch, HyperscanRuntimeError> {
    let mut scratch = Scratch::new();
    scratch.setup_for_db(self)?;
    Ok(scratch)
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::*};
  /// use futures_util::TryStreamExt;
  ///
  /// let expr: Expression = "(he)ll".parse()?;
  /// let db = Database::compile(&expr, Flags::UTF8, Mode::BLOCK, Platform::get())?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "hello".into(), |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["hell"]);
  /// # Ok(())
  /// # })}
  /// ```
  #[cfg(feature = "compile")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
  pub fn compile(
    expression: &Expression,
    flags: Flags,
    mode: Mode,
    platform: &Platform,
  ) -> Result<Self, HyperscanCompileError> {
    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile(
          expression.as_ptr(),
          flags.into_native(),
          mode.into_native(),
          platform.as_ref_native(),
          &mut db,
          &mut compile_err,
        )
      },
      compile_err,
    )?;
    Ok(unsafe { Self::from_native(db) })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::*};
  /// use futures_util::TryStreamExt;
  ///
  /// let expr: Literal = "he\0ll".parse()?;
  /// let db = Database::compile_literal(&expr, Flags::default(), Mode::BLOCK, Platform::get())?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "he\0llo".into(), |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["he\0ll"]);
  /// # Ok(())
  /// # })}
  /// ```
  #[cfg(feature = "compile")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
  pub fn compile_literal(
    literal: &Literal,
    flags: Flags,
    mode: Mode,
    platform: &Platform,
  ) -> Result<Self, HyperscanCompileError> {
    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile_lit(
          literal.as_ptr(),
          flags.into_native(),
          literal.as_bytes().len(),
          mode.into_native(),
          platform.as_ref_native(),
          &mut db,
          &mut compile_err,
        )
      },
      compile_err,
    )?;
    Ok(unsafe { Self::from_native(db) })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::*};
  /// use futures_util::TryStreamExt;
  ///
  /// let a_expr: Expression = "a+".parse()?;
  /// let b_expr: Expression = "b+".parse()?;
  ///
  /// // Example of providing ExprExt info (not available in ::compile()!):
  /// let ext = ExprExt::from_min_length(1);
  ///
  /// let expr_set = ExpressionSet::from_exprs([&a_expr, &b_expr])
  ///   .with_flags([Flags::UTF8, Flags::UTF8])
  ///   .with_ids([ExprId(1), ExprId(2)])
  ///   .with_exts([None, Some(&ext)]);
  ///
  /// let db = Database::compile_multi(&expr_set, Mode::BLOCK, Platform::get())?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "aardvark".into(), |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "aa", "aardva"]);
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "imbibe".into(), |_| MatchResult::Continue)
  ///   .and_then(|m| async move { Ok(unsafe { m.source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["imb", "imbib"]);
  /// # Ok(())
  /// # })}
  /// ```
  #[cfg(feature = "compile")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
  pub fn compile_multi(
    expression_set: &ExpressionSet,
    mode: Mode,
    platform: &Platform,
  ) -> Result<Self, HyperscanCompileError> {
    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        if let Some(exts_ptr) = expression_set.exts_ptr() {
          hs::hs_compile_ext_multi(
            expression_set.expressions_ptr(),
            expression_set.flags_ptr(),
            expression_set.ids_ptr(),
            exts_ptr,
            expression_set.num_elements(),
            mode.into_native(),
            platform.as_ref_native(),
            &mut db,
            &mut compile_err,
          )
        } else {
          hs::hs_compile_multi(
            expression_set.expressions_ptr(),
            expression_set.flags_ptr(),
            expression_set.ids_ptr(),
            expression_set.num_elements(),
            mode.into_native(),
            platform.as_ref_native(),
            &mut db,
            &mut compile_err,
          )
        }
      },
      compile_err,
    )?;
    Ok(unsafe { Self::from_native(db) })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, database::*, matchers::{*, contiguous_slice::*}};
  /// use futures_util::TryStreamExt;
  ///
  /// let hell_lit: Literal = "he\0ll".parse()?;
  /// let free_lit: Literal = "fr\0e\0e".parse()?;
  /// let lit_set = LiteralSet::from_lits([&hell_lit, &free_lit])
  ///   .with_flags([Flags::default(), Flags::default()])
  ///   .with_ids([ExprId(2), ExprId(1)]);
  ///
  /// let db = Database::compile_multi_literal(&lit_set, Mode::BLOCK, Platform::get())?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let matches: Vec<(u32, &str)> = scratch
  ///   .scan(&db, "he\0llo".into(), |_| MatchResult::Continue)
  ///   .and_then(|Match { id: ExpressionIndex(id), source, .. }| async move {
  ///     Ok((id, unsafe { source.as_str() }))
  ///   })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &[(2, "he\0ll")]);
  ///
  /// let matches: Vec<(u32, &str)> = scratch
  ///   .scan(&db, "fr\0e\0edom".into(), |_| MatchResult::Continue)
  ///   .and_then(|Match { id: ExpressionIndex(id), source, .. }| async move {
  ///     Ok((id, unsafe { source.as_str() }))
  ///   })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &[(1, "fr\0e\0e")]);
  /// # Ok(())
  /// # })}
  /// ```
  #[cfg(feature = "compile")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
  pub fn compile_multi_literal(
    literal_set: &LiteralSet,
    mode: Mode,
    platform: &Platform,
  ) -> Result<Self, HyperscanCompileError> {
    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    HyperscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile_lit_multi(
          literal_set.literals_ptr(),
          literal_set.flags_ptr(),
          literal_set.ids_ptr(),
          literal_set.lengths_ptr(),
          literal_set.num_elements(),
          mode.into_native(),
          platform.as_ref_native(),
          &mut db,
          &mut compile_err,
        )
      },
      compile_err,
    )?;
    Ok(unsafe { Self::from_native(db) })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*};
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let db = expr.compile(Flags::UTF8, Mode::BLOCK)?;
  /// let db_size = db.database_size()?;
  ///
  /// // Size may vary across architectures:
  /// assert_eq!(db_size, 936);
  /// assert!(db_size > 500);
  /// assert!(db_size < 2000);
  /// # Ok(())
  /// # }
  /// ```
  pub fn database_size(&self) -> Result<usize, HyperscanRuntimeError> {
    let mut ret: MaybeUninit<usize> = MaybeUninit::uninit();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_database_size(self.as_ref_native(), ret.as_mut_ptr())
    })?;
    Ok(unsafe { ret.assume_init() })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*};
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let db = expr.compile(Flags::UTF8, Mode::STREAM)?;
  /// let stream_size = db.stream_size()?;
  ///
  /// // Size may vary across architectures:
  /// assert_eq!(stream_size, 18);
  /// assert!(stream_size > 10);
  /// assert!(stream_size < 20);
  /// # Ok(())
  /// # }
  /// ```
  pub fn stream_size(&self) -> Result<usize, HyperscanRuntimeError> {
    let mut ret: MaybeUninit<usize> = MaybeUninit::uninit();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_stream_size(self.as_ref_native(), ret.as_mut_ptr())
    })?;
    Ok(unsafe { ret.assume_init() })
  }

  pub fn info(&self) -> Result<DbInfo, HyperscanRuntimeError> { DbInfo::extract_db_info(self) }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, matchers::{*, contiguous_slice::*}};
  /// use futures_util::TryStreamExt;
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?.serialize()?.deserialize_db()?;
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "aardvark".into(), |_| MatchResult::Continue)
  ///   .and_then(|Match { source, .. }| async move { Ok(unsafe { source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "aa", "a"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn serialize(&self) -> Result<SerializedDb<'static>, HyperscanRuntimeError> {
    SerializedDb::serialize_db(self)
  }

  pub unsafe fn try_drop(&mut self) -> Result<(), HyperscanRuntimeError> {
    HyperscanRuntimeError::from_native(unsafe { hs::hs_free_database(self.as_mut_native()) })
  }
}

impl ops::Drop for Database {
  fn drop(&mut self) {
    unsafe {
      self.try_drop().unwrap();
    }
  }
}

unsafe impl Send for Database {}
unsafe impl Sync for Database {}

#[derive(Debug)]
pub struct MiscAllocation {
  data: *mut u8,
  len: usize,
}

unsafe impl Send for MiscAllocation {}
unsafe impl Sync for MiscAllocation {}

impl MiscAllocation {
  pub const fn as_ptr(&self) -> *mut u8 { self.data }

  pub const fn len(&self) -> usize { self.len }

  pub const fn is_empty(&self) -> bool { self.len() == 0 }

  pub const fn as_slice(&self) -> &[u8] { unsafe { slice::from_raw_parts(self.data, self.len) } }

  pub fn as_mut_slice(&mut self) -> &mut [u8] {
    unsafe { slice::from_raw_parts_mut(self.data, self.len) }
  }

  pub unsafe fn free(&mut self) { crate::free_misc(self.data) }
}

impl ops::Drop for MiscAllocation {
  fn drop(&mut self) {
    unsafe {
      self.free();
    }
  }
}

#[derive(Debug)]
pub struct DbInfo(pub MiscAllocation);

impl DbInfo {
  const fn without_null(&self) -> impl slice::SliceIndex<[u8], Output=[u8]> { ..(self.0.len() - 1) }

  pub fn as_str(&self) -> &str {
    unsafe { str::from_utf8_unchecked(&self.0.as_slice()[self.without_null()]) }
  }

  pub fn as_mut_str(&mut self) -> &mut str {
    let without_null = self.without_null();
    unsafe { str::from_utf8_unchecked_mut(&mut self.0.as_mut_slice()[without_null]) }
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*, database::*};
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let db = expr.compile(Flags::UTF8, Mode::BLOCK)?;
  /// let info = DbInfo::extract_db_info(&db)?;
  /// assert_eq!(info.as_str(), "Version: 5.4.2 Features: AVX2 Mode: BLOCK");
  /// # Ok(())
  /// # }
  /// ```
  pub fn extract_db_info(db: &Database) -> Result<Self, HyperscanRuntimeError> {
    let mut info: MaybeUninit<*mut c_char> = MaybeUninit::uninit();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_database_info(db.as_ref_native(), info.as_mut_ptr())
    })?;
    let info = unsafe { info.assume_init() };
    let len = unsafe { CStr::from_ptr(info) }.to_bytes_with_nul().len();
    assert!(len > 0);

    let ret = MiscAllocation {
      data: unsafe { mem::transmute(info) },
      len,
    };

    Ok(Self(ret))
  }
}

#[derive(Debug)]
pub enum DbAllocation<'a> {
  Misc(MiscAllocation),
  Rust(Cow<'a, [u8]>),
}

impl<'a> DbAllocation<'a> {
  pub fn as_ptr(&self) -> *const u8 {
    match self {
      Self::Misc(misc) => misc.as_ptr(),
      Self::Rust(cow) => cow.as_ptr(),
    }
  }

  pub fn len(&self) -> usize {
    match self {
      Self::Misc(misc) => misc.len(),
      Self::Rust(cow) => cow.len(),
    }
  }

  pub fn is_empty(&self) -> bool { self.len() == 0 }

  pub fn as_slice(&self) -> &[u8] { unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) } }
}

impl DbAllocation<'static> {
  pub fn from_cloned_data(s: &DbAllocation) -> Self {
    let newly_allocated: Vec<u8> = s.as_slice().to_vec();
    Self::Rust(Cow::Owned(newly_allocated))
  }
}

#[derive(Debug)]
#[repr(transparent)]
pub struct SerializedDb<'a>(pub DbAllocation<'a>);

impl SerializedDb<'static> {
  pub fn serialize_db(db: &Database) -> Result<Self, HyperscanRuntimeError> {
    let mut data = ptr::null_mut();
    let mut len: usize = 0;

    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_serialize_database(db.as_ref_native(), &mut data, &mut len)
    })?;

    let data = data as *mut u8;

    Ok(Self(DbAllocation::Misc(MiscAllocation { data, len })))
  }

  pub fn from_cloned_data(s: &SerializedDb) -> Self {
    let SerializedDb(ref s) = s;
    Self(DbAllocation::from_cloned_data(s))
  }
}

impl<'a> SerializedDb<'a> {
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> {
  /// use hyperscan::{expression::*, flags::*};
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let serialized_db = expr.compile(Flags::UTF8, Mode::BLOCK)?.serialize()?;
  /// let info = serialized_db.extract_db_info()?;
  /// assert_eq!(info.as_str(), "Version: 5.4.2 Features: AVX2 Mode: BLOCK");
  /// # Ok(())
  /// # }
  /// ```
  pub fn extract_db_info(&self) -> Result<DbInfo, HyperscanRuntimeError> {
    let mut info = ptr::null_mut();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_serialized_database_info(self.as_ptr(), self.len(), &mut info)
    })?;
    let len = unsafe { CStr::from_ptr(info) }.to_bytes_with_nul().len();
    assert!(len > 0);

    let ret = MiscAllocation {
      data: info as *mut u8,
      len,
    };

    Ok(DbInfo(ret))
  }

  fn as_ptr(&self) -> *const c_char { unsafe { mem::transmute(self.0.as_ptr()) } }

  pub fn len(&self) -> usize { self.0.len() }

  pub fn is_empty(&self) -> bool { self.0.is_empty() }

  pub fn deserialize_db(&self) -> Result<Database, HyperscanRuntimeError> {
    let mut deserialized: MaybeUninit<*mut hs::hs_database> = MaybeUninit::uninit();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_deserialize_database(self.as_ptr(), self.len(), deserialized.as_mut_ptr())
    })?;
    let deserialized = unsafe { deserialized.assume_init() };
    Ok(unsafe { Database::from_native(deserialized) })
  }

  /// Return the size of the allocation necessary for a subsequent call to
  /// [`Self::deserialize_db_at()`].
  pub fn deserialized_size(&self) -> Result<usize, HyperscanRuntimeError> {
    let mut deserialized_size: MaybeUninit<usize> = MaybeUninit::uninit();
    HyperscanRuntimeError::from_native(unsafe {
      hs::hs_serialized_database_size(self.as_ptr(), self.len(), deserialized_size.as_mut_ptr())
    })?;
    let deserialized_size = unsafe { deserialized_size.assume_init() };
    Ok(deserialized_size)
  }

  /// Like [`Self::deserialize_db()`], but points into an existing allocation
  /// instead of making a new allocation through the allocator from
  /// [`crate::alloc::set_db_allocator()`]!
  ///
  /// **Safety: `db` must point to an allocation at least
  /// [`Self::deserialized_size()`] in size!**
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::HyperscanError> { tokio_test::block_on(async {
  /// use hyperscan::{expression::*, flags::*, matchers::{*, contiguous_slice::*}, database::*};
  /// use futures_util::TryStreamExt;
  /// use std::mem;
  ///
  /// let expr: Expression = "a+".parse()?;
  /// let serialized_db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?.serialize()?;
  ///
  /// // Allocate a vector with sufficient capacity for the deserialized db:
  /// let mut db_data: Vec<u8> = Vec::with_capacity(serialized_db.deserialized_size()?);
  /// let db = unsafe {
  ///   let db_ptr: *mut NativeDb = mem::transmute(db_data.as_mut_ptr());
  ///   serialized_db.deserialize_db_at(db_ptr)?;
  ///   // Wrap in ManuallyDrop to avoid freeing memory owned by the `db_data` vector.
  ///   mem::ManuallyDrop::new(Database::from_native(db_ptr))
  /// };
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan(&db, "aardvark".into(), |_| MatchResult::Continue)
  ///   .and_then(|Match { source, .. }| async move { Ok(unsafe { source.as_str() }) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["a", "aa", "a"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub unsafe fn deserialize_db_at(&self, db: *mut NativeDb) -> Result<(), HyperscanRuntimeError> {
    HyperscanRuntimeError::from_native(hs::hs_deserialize_database_at(
      self.as_ptr(),
      self.len(),
      db,
    ))
  }
}

#[cfg(feature = "compile")]
#[cfg_attr(docsrs, doc(cfg(feature = "compile")))]
#[derive(Debug, Copy, Clone)]
#[repr(transparent)]
pub struct Platform(hs::hs_platform_info);

#[cfg(feature = "compile")]
static CACHED_PLATFORM: Lazy<Platform> = Lazy::new(|| Platform::populate().unwrap());

#[cfg(feature = "compile")]
impl Platform {
  pub fn tune(&self) -> TuneFamily { TuneFamily::from_native(self.0.tune) }

  pub fn set_tune(&mut self, tune: TuneFamily) { self.0.tune = tune.into_native(); }

  pub fn cpu_features(&self) -> CpuFeatures { CpuFeatures::from_native(self.0.cpu_features) }

  pub fn set_cpu_features(&mut self, cpu_features: CpuFeatures) {
    self.0.cpu_features = cpu_features.into_native();
  }

  fn populate() -> Result<Self, HyperscanRuntimeError> {
    let mut s = mem::MaybeUninit::<hs::hs_platform_info>::uninit();
    HyperscanRuntimeError::from_native(unsafe { hs::hs_populate_platform(s.as_mut_ptr()) })?;
    Ok(unsafe { Self(s.assume_init()) })
  }

  pub fn get() -> &'static Self { &CACHED_PLATFORM }

  pub(crate) fn as_ref_native(&self) -> &hs::hs_platform_info { &self.0 }
}


#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::Platform;
  use crate::{
    error::chimera::{ChimeraCompileError, ChimeraRuntimeError},
    expression::chimera::{ChimeraExpression, ChimeraExpressionSet, ChimeraMatchLimits},
    flags::chimera::{ChimeraFlags, ChimeraMode},
    hs,
    state::chimera::ChimeraScratch,
  };

  use cfg_if::cfg_if;

  use std::{
    ffi::CStr,
    mem::MaybeUninit,
    ops,
    os::raw::{c_char, c_void},
    ptr,
  };


  #[derive(Debug)]
  #[repr(transparent)]
  pub struct ChimeraDb(*mut NativeChimeraDb);

  pub type NativeChimeraDb = hs::ch_database;

  impl ChimeraDb {
    pub const unsafe fn from_native(p: *mut NativeChimeraDb) -> Self { Self(p) }

    pub fn as_ref_native(&self) -> &hs::ch_database { unsafe { &*self.0 } }

    pub fn as_mut_native(&mut self) -> &mut hs::ch_database { unsafe { &mut *self.0 } }

    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> { tokio_test::block_on(async {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*, database::{*, chimera::*}};
    ///
    /// let expr: ChimeraExpression = "(he)ll".parse()?;
    /// let _db = ChimeraDb::compile(&expr, ChimeraFlags::UTF8, ChimeraMode::NOGROUPS, Platform::get())?;
    /// # Ok(())
    /// # })}
    /// ```
    pub fn compile(
      expression: &ChimeraExpression,
      flags: ChimeraFlags,
      mode: ChimeraMode,
      platform: &Platform,
    ) -> Result<Self, ChimeraCompileError> {
      let mut db = ptr::null_mut();
      let mut compile_err = ptr::null_mut();
      ChimeraRuntimeError::copy_from_native_compile_error(
        unsafe {
          hs::ch_compile(
            expression.as_ptr(),
            flags.into_native(),
            mode.into_native(),
            platform.as_ref_native(),
            &mut db,
            &mut compile_err,
          )
        },
        compile_err,
      )?;
      Ok(unsafe { Self::from_native(db) })
    }

    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> { tokio_test::block_on(async {
    /// use hyperscan::{expression::{*, chimera::*}, flags::chimera::*, database::{*, chimera::*}, matchers::chimera::*};
    /// use futures_util::TryStreamExt;
    ///
    /// let a_expr: ChimeraExpression = "a+".parse()?;
    /// let b_expr: ChimeraExpression = "b+".parse()?;
    /// let exprs = ChimeraExpressionSet::from_exprs([&a_expr, &b_expr])
    ///   .with_flags([ChimeraFlags::UTF8, ChimeraFlags::UTF8])
    ///   .with_ids([ExprId(1), ExprId(2)])
    ///   .with_limits(ChimeraMatchLimits { match_limit: 30, match_limit_recursion: 30 });
    /// let db = ChimeraDb::compile_multi(&exprs, ChimeraMode::NOGROUPS, Platform::get())?;
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// let matches: Vec<&str> = scratch.scan::<TrivialChimeraScanner>(
    ///   &db,
    ///   "aardvark imbibbe".into(),
    /// ).and_then(|ChimeraMatch { source, .. }| async move { Ok(unsafe { source.as_str() }) })
    ///  .try_collect().await?;
    /// assert_eq!(&matches, &["aa", "a", "b", "bb"]);
    /// # Ok(())
    /// # })}
    /// ```
    pub fn compile_multi(
      exprs: &ChimeraExpressionSet,
      mode: ChimeraMode,
      platform: &Platform,
    ) -> Result<Self, ChimeraCompileError> {
      let mut db = ptr::null_mut();
      let mut compile_err = ptr::null_mut();
      ChimeraRuntimeError::copy_from_native_compile_error(
        unsafe {
          if let Some(ChimeraMatchLimits {
            match_limit,
            match_limit_recursion,
          }) = exprs.limits()
          {
            hs::ch_compile_ext_multi(
              exprs.expressions_ptr(),
              exprs.flags_ptr(),
              exprs.ids_ptr(),
              exprs.num_elements(),
              mode.into_native(),
              match_limit,
              match_limit_recursion,
              platform.as_ref_native(),
              &mut db,
              &mut compile_err,
            )
          } else {
            hs::ch_compile_multi(
              exprs.expressions_ptr(),
              exprs.flags_ptr(),
              exprs.ids_ptr(),
              exprs.num_elements(),
              mode.into_native(),
              platform.as_ref_native(),
              &mut db,
              &mut compile_err,
            )
          }
        },
        compile_err,
      )?;
      Ok(unsafe { Self::from_native(db) })
    }

    pub fn get_db_size(&self) -> Result<usize, ChimeraRuntimeError> {
      let mut database_size = MaybeUninit::<usize>::uninit();
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_database_size(self.as_ref_native(), database_size.as_mut_ptr())
      })?;
      Ok(unsafe { database_size.assume_init() })
    }

    pub fn info(&self) -> Result<ChimeraDbInfo, ChimeraRuntimeError> {
      ChimeraDbInfo::extract_db_info(self)
    }

    pub fn allocate_scratch(&self) -> Result<ChimeraScratch, ChimeraRuntimeError> {
      let mut scratch = ChimeraScratch::new();
      scratch.setup_for_db(self)?;
      Ok(scratch)
    }

    pub unsafe fn try_drop(&mut self) -> Result<(), ChimeraRuntimeError> {
      ChimeraRuntimeError::from_native(hs::ch_free_database(self.as_mut_native()))
    }
  }

  impl ops::Drop for ChimeraDb {
    fn drop(&mut self) {
      unsafe {
        self.try_drop().unwrap();
      }
    }
  }

  #[derive(Debug, Clone)]
  pub struct ChimeraDbInfo(pub String);

  impl ChimeraDbInfo {
    ///```
    /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
    /// use hyperscan::{expression::chimera::*, flags::chimera::*, database::chimera::*};
    ///
    /// let expr: ChimeraExpression = "a+".parse()?;
    /// let db = expr.compile(ChimeraFlags::UTF8, ChimeraMode::NOGROUPS)?;
    /// let info = ChimeraDbInfo::extract_db_info(&db)?;
    /// assert_eq!(&info.0, "Chimera Version: 5.4.2 Features: AVX2 Mode: BLOCK");
    /// # Ok(())
    /// # }
    /// ```
    pub fn extract_db_info(db: &ChimeraDb) -> Result<Self, ChimeraRuntimeError> {
      let mut info: MaybeUninit<*mut c_char> = MaybeUninit::uninit();
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_database_info(db.as_ref_native(), info.as_mut_ptr())
      })?;
      let info = unsafe { info.assume_init() };
      let ret = unsafe { CStr::from_ptr(info) }
      .to_string_lossy()
      /* FIXME: avoid copying! */
      .to_string();
      unsafe {
        cfg_if! {
          if #[cfg(feature = "static")] {
            crate::alloc::chimera::chimera_misc_free_func(info as *mut c_void);
          } else {
            libc::free(info as *mut c_void);
          }
        }
      }
      Ok(Self(ret))
    }
  }
}
