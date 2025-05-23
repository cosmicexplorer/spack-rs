/* Copyright 2022-2024 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Compile state machines from expressions or deserialize them from bytes.
//!
//! Vectorscan supports two distinct types of databases:
//! - [`Database`]: from the base vectorscan library and supports [`Expression`]
//!   and [`Literal`] patterns.
//! - [`chimera::ChimeraDb`]: from the chimera library and supports
//!   [`ChimeraExpression`](crate::expression::chimera::ChimeraExpression)
//!   patterns.
//!
//! Each database type serves as the entry point to the pattern compiler
//! methods, such as [`Database::compile()`] and
//! [`chimera::ChimeraDb::compile()`].
//!
//! # Database Instantiation
//! The base vectorscan library offers a serialization interface for database
//! objects which allows them to be transferred across hosts. The
//! [`SerializedDb`] type provides an interface to locate serialized data from
//! multiple locations. Consumers of this crate which disable the `"compiler"`
//! feature can still search against strings by deserializing a database from
//! bytes.
//!
//! The chimera library does not support database serialization, so databases
//! must be created by compilation.

#[cfg(feature = "stream")]
use crate::stream::LiveStream;
#[cfg(feature = "compiler")]
use crate::{
  error::VectorscanCompileError,
  expression::{Expression, ExpressionSet, Literal, LiteralSet},
  flags::{platform::Platform, Flags, Mode},
};
use crate::{error::VectorscanRuntimeError, hs, state::Scratch};

use std::{
  cmp,
  ffi::CStr,
  fmt, hash,
  mem::{self, MaybeUninit},
  ops,
  os::raw::c_char,
  ptr, slice, str,
};

/// Pointer type for db allocations used in [`Database#Managing
/// Allocations`](Database#managing-allocations).
pub type NativeDb = hs::hs_database;

/// Read-only description of an in-memory state machine.
///
/// This type also serves as the entry point to the various types of [pattern
/// compilers](#pattern-compilers), including literals, sets, and literal sets.
#[derive(Debug)]
#[repr(transparent)]
pub struct Database(*mut NativeDb);

/// # Convenience Methods
/// These methods prepare some resource within a new heap allocation and are
/// useful for doctests and examples.
///
/// ## Scratch Setup
/// Databases already require their own heap allocation, which can be managed
/// with the methods in [Managing Allocations](#managing-allocations). However,
/// databases also impose a sort of implicit dynamic lifetime constraint on
/// [`Scratch`] objects, which must be initialized against a db with
/// [`Scratch::setup_for_db()`] before vectorscan can do any searching.
///
/// It is encouraged to re-use [`Scratch`] objects across databases where
/// possible to minimize unnecessary allocations, but
/// [`Self::allocate_scratch()`] is provided as a convenience method to quickly
/// produce a 1:1 db:scratch mapping.
///
/// ## Serialization
/// While [`SerializedDb`] offers a rich interface to wrap serialized bytes from
/// a variety of sources with [`alloc::DbAllocation`], [`Self::serialize()`]
/// simply returns a newly allocated region of bytes.
impl Database {
  /// Call [`Scratch::setup_for_db()`] on a newly allocated [`Scratch::blank`].
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, matchers::*};
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   scratch
  ///     .scan_sync(&db, "aardvark".into(), |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["a", "aa", "a"]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn allocate_scratch(&self) -> Result<Scratch, VectorscanRuntimeError> {
    let mut scratch = Scratch::blank();
    scratch.setup_for_db(self)?;
    Ok(scratch)
  }

  /// Call [`LiveStream::open()`] on `self`.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, matchers::*, stream::*};
  ///   use std::ops::Range;
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::STREAM | Mode::SOM_HORIZON_SMALL)?;
  ///   let scratch = db.allocate_scratch()?;
  ///   let live = db.allocate_stream()?;
  ///
  ///   let data = "aardvark";
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   let mut match_fn = |StreamMatch { range, .. }| {
  ///     let range: Range<usize> = range.into();
  ///     matches.push(&data[range]);
  ///     MatchResult::Continue
  ///   };
  ///   {
  ///     let matcher = StreamMatcher::new(&mut match_fn);
  ///     let mut sink = ScratchStreamSink::new(live, matcher, scratch);
  ///
  ///     sink.scan(data.into())?;
  ///     sink.flush_eod()?;
  ///   }
  ///   assert_eq!(&matches, &["a", "aa", "a"]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  #[cfg(feature = "stream")]
  #[cfg_attr(docsrs, doc(cfg(feature = "stream")))]
  pub fn allocate_stream(&self) -> Result<LiveStream, VectorscanRuntimeError> {
    LiveStream::open(self)
  }

  /// Allocate a new memory region and serialize this in-memory state machine
  /// into it.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, matchers::*};
  ///
  ///   // Create a db to match against:
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///
  ///   // Serialize and deserialize the db:
  ///   let db = db.serialize()?.deserialize_db()?;
  ///   let mut scratch = db.allocate_scratch()?;
  ///
  ///   // Search against the db:
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   scratch
  ///     .scan_sync(&db, "aardvark".into(), |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["a", "aa", "a"]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn serialize(&self) -> Result<SerializedDb<'static>, VectorscanRuntimeError> {
    SerializedDb::serialize_db(self)
  }
}

/// # Pattern Compilers
/// Vectorscan supports compiling state machines for PCRE-like and literal
/// pattern strings, as well as parallel sets of those patterns (although note
/// that literal and non-literal patterns cannot be mixed). Each compile method
/// supports a subset of all [`Flags`] arguments, documented in each method.
///
/// ## Platform Compatibility
/// Each method also accepts an optional [`Platform`] object,
/// which is used to select processor features to compile the database for.
/// While the default of [`None`] will enable all features available to the
/// current processor, some features can be disabled in order to produce a
/// database which can execute on a wider variety of target platforms
/// after being deserialized from a remote source.
///
///```
/// #[cfg(all(feature = "compiler", feature = "stream"))]
/// fn main() -> Result<(), vectorscan::error::VectorscanError> {
///   use vectorscan::{expression::*, flags::{*, platform::*}, database::*};
///   use std::slice;
///
///   let expr: Expression = "a+".parse()?;
///
///   // Verify that the current platform has AVX2 instructions, and make a db:
///   let plat = Platform::local()?;
///   assert!(plat.cpu_features.contains(&CpuFeatures::AVX2));
///   assert!(plat != Platform::GENERIC);
///   let db_with_avx2 = Database::compile(
///     &expr,
///     Flags::default(),
///     Mode::STREAM,
///     Some(&plat),
///   )?;
///
///   // The only specialized instructions we have available are AVX2:
///   assert_eq!(CpuFeatures::NONE, plat.cpu_features & !CpuFeatures::AVX2);
///   // Avoid using AVX2 instructions:
///   let db_no_avx2 = Database::compile(
///     &expr,
///     Flags::default(),
///     Mode::STREAM,
///     Some(&Platform::GENERIC),
///   )?;
///
///   // Instruction selection does not affect the size of the state machine:
///   assert!(db_with_avx2.database_size()? == db_no_avx2.database_size()?);
///   assert!(db_with_avx2.stream_size()? == db_no_avx2.stream_size()?);
///
///   // Now create a db with None for the platform:
///   let db_local = Database::compile(&expr, Flags::default(), Mode::STREAM, None)?;
///   assert!(db_with_avx2.database_size()? == db_local.database_size()?);
///   let n = db_with_avx2.database_size()?;
///
///   // Using None produces the same db as Platform::local():
///   assert!(db_with_avx2.info()? == db_local.info()?);
///   assert!(db_no_avx2.info()? != db_local.info()?);
///
///   // The "same" db does *not* apply to the in-memory representation:
///   let db_data_1 = unsafe { slice::from_raw_parts(
///     db_with_avx2.as_ref_native() as *const NativeDb as *const u8,
///     n,
///   )};
///   let db_data_2 = unsafe { slice::from_raw_parts(
///     db_no_avx2.as_ref_native() as *const NativeDb as *const u8,
///     n,
///   )};
///   let db_data_3 = unsafe { slice::from_raw_parts(
///     db_local.as_ref_native() as *const NativeDb as *const u8,
///     n,
///   )};
///   assert!(db_data_1 != db_data_3);
///   assert!(db_data_1 != db_data_2);
///   Ok(())
/// }
/// # #[cfg(not(all(feature = "compiler", feature = "stream")))]
/// # fn main() {}
/// ```
///
/// ## Dynamic Memory Allocation
/// These methods allocate a new region of memory using the db allocator (which
/// can be overridden with [`crate::alloc::set_db_allocator()`]). That
/// allocation can be manipulated as described in [Managing
/// Allocations](#managing-allocations).
#[cfg(feature = "compiler")]
#[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
impl Database {
  /// Single pattern compiler.
  ///
  /// # Accepted Flags
  /// - [`CASELESS`](Flags::CASELESS)
  /// - [`DOTALL`](Flags::DOTALL)
  /// - [`MULTILINE`](Flags::MULTILINE)
  /// - [`SINGLEMATCH`](Flags::SINGLEMATCH)
  /// - [`ALLOWEMPTY`](Flags::ALLOWEMPTY)
  /// - [`UTF8`](Flags::UTF8)
  /// - [`UCP`](Flags::UCP)
  /// - [`PREFILTER`](Flags::PREFILTER)
  /// - [`SOM_LEFTMOST`](Flags::SOM_LEFTMOST)
  /// - [`COMBINATION`](Flags::COMBINATION)
  /// - [`QUIET`](Flags::QUIET)
  ///
  ///```
  /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
  /// use vectorscan::{expression::*, flags::*, database::*, matchers::*};
  ///
  /// let expr: Expression = "hell(o)?".parse()?;
  /// let db = Database::compile(&expr, Flags::default(), Mode::BLOCK, None)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<&str> = Vec::new();
  /// scratch
  ///   .scan_sync(&db, "hello".into(), |m| {
  ///     matches.push(unsafe { m.source.as_str() });
  ///     MatchResult::Continue
  ///   })?;
  /// assert_eq!(&matches, &["hell", "hello"]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn compile(
    expression: &Expression,
    flags: Flags,
    mode: Mode,
    platform: Option<&Platform>,
  ) -> Result<Self, VectorscanCompileError> {
    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    let platform: Option<hs::hs_platform_info> = platform.cloned().map(Platform::into_native);
    VectorscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile(
          expression.as_ptr(),
          flags.into_native(),
          mode.into_native(),
          platform
            .as_ref()
            .map(|p| p as *const hs::hs_platform_info)
            .unwrap_or(ptr::null()),
          &mut db,
          &mut compile_err,
        )
      },
      compile_err,
    )?;
    Ok(unsafe { Self::from_native(db) })
  }

  /// Multiple pattern compiler.
  ///
  /// # Accepted Flags
  /// - [`CASELESS`](Flags::CASELESS)
  /// - [`DOTALL`](Flags::DOTALL)
  /// - [`MULTILINE`](Flags::MULTILINE)
  /// - [`SINGLEMATCH`](Flags::SINGLEMATCH)
  /// - [`ALLOWEMPTY`](Flags::ALLOWEMPTY)
  /// - [`UTF8`](Flags::UTF8)
  /// - [`UCP`](Flags::UCP)
  /// - [`PREFILTER`](Flags::PREFILTER)
  /// - [`SOM_LEFTMOST`](Flags::SOM_LEFTMOST)
  /// - [`COMBINATION`](Flags::COMBINATION)
  /// - [`QUIET`](Flags::QUIET)
  ///
  ///```
  /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
  /// use vectorscan::{expression::*, flags::*, database::*, matchers::*};
  ///
  /// let a_expr: Expression = "a+".parse()?;
  /// let b_expr: Expression = "b+".parse()?;
  ///
  /// // Example of providing ExprExt info (not available in ::compile()!):
  /// let ext = ExprExt::from_min_length(1);
  ///
  /// let expr_set = ExpressionSet::from_exprs([&a_expr, &b_expr])
  ///   .with_ids([ExprId(1), ExprId(2)])
  ///   .with_exts([None, Some(&ext)]);
  ///
  /// let db = Database::compile_multi(&expr_set, Mode::BLOCK, None)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<&str> = Vec::new();
  /// scratch
  ///   .scan_sync(&db, "aardvark".into(), |m| {
  ///     matches.push(unsafe { m.source.as_str() });
  ///     MatchResult::Continue
  ///   })?;
  /// assert_eq!(&matches, &["a", "aa", "aardva"]);
  ///
  /// matches.clear();
  /// scratch
  ///   .scan_sync(&db, "imbibe".into(), |m| {
  ///     matches.push(unsafe { m.source.as_str() });
  ///     MatchResult::Continue
  ///   })?;
  /// assert_eq!(&matches, &["imb", "imbib"]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn compile_multi(
    expression_set: &ExpressionSet,
    mode: Mode,
    platform: Option<&Platform>,
  ) -> Result<Self, VectorscanCompileError> {
    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    let platform: Option<hs::hs_platform_info> = platform.cloned().map(Platform::into_native);
    VectorscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        if let Some(exts_ptr) = expression_set.exts_ptr() {
          hs::hs_compile_ext_multi(
            expression_set.expressions_ptr(),
            expression_set.flags_ptr(),
            expression_set.ids_ptr(),
            exts_ptr,
            expression_set.num_elements(),
            mode.into_native(),
            platform
              .as_ref()
              .map(|p| p as *const hs::hs_platform_info)
              .unwrap_or(ptr::null()),
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
            platform
              .as_ref()
              .map(|p| p as *const hs::hs_platform_info)
              .unwrap_or(ptr::null()),
            &mut db,
            &mut compile_err,
          )
        }
      },
      compile_err,
    )?;
    Ok(unsafe { Self::from_native(db) })
  }

  /// Single literal compiler.
  ///
  /// # Accepted Flags
  /// - [`CASELESS`](Flags::CASELESS)
  /// - [`SINGLEMATCH`](Flags::SINGLEMATCH)
  /// - [`SOM_LEFTMOST`](Flags::SOM_LEFTMOST)
  ///
  ///```
  /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
  /// use vectorscan::{expression::*, flags::*, database::*, matchers::*};
  ///
  /// let expr: Literal = "he\0ll".parse()?;
  /// let db = Database::compile_literal(&expr, Flags::default(), Mode::BLOCK, None)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<&str> = Vec::new();
  /// scratch
  ///   .scan_sync(&db, "he\0llo".into(), |m| {
  ///     matches.push(unsafe { m.source.as_str() });
  ///     MatchResult::Continue
  ///   })?;
  /// assert_eq!(&matches, &["he\0ll"]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn compile_literal(
    literal: &Literal,
    flags: Flags,
    mode: Mode,
    platform: Option<&Platform>,
  ) -> Result<Self, VectorscanCompileError> {
    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    let platform: Option<hs::hs_platform_info> = platform.cloned().map(Platform::into_native);
    VectorscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile_lit(
          literal.as_ptr(),
          flags.into_native(),
          literal.as_bytes().len(),
          mode.into_native(),
          platform
            .as_ref()
            .map(|p| p as *const hs::hs_platform_info)
            .unwrap_or(ptr::null()),
          &mut db,
          &mut compile_err,
        )
      },
      compile_err,
    )?;
    Ok(unsafe { Self::from_native(db) })
  }

  /// Multiple literal compiler.
  ///
  /// # Accepted Flags
  /// - [`CASELESS`](Flags::CASELESS)
  /// - [`SINGLEMATCH`](Flags::SINGLEMATCH)
  /// - [`SOM_LEFTMOST`](Flags::SOM_LEFTMOST)
  ///
  ///```
  /// # fn main() -> Result<(), vectorscan::error::VectorscanError> {
  /// use vectorscan::{expression::*, flags::*, database::*, matchers::*};
  ///
  /// let hell_lit: Literal = "he\0ll".parse()?;
  /// let free_lit: Literal = "fr\0e\0e".parse()?;
  /// let lit_set = LiteralSet::from_lits([&hell_lit, &free_lit])
  ///   .with_flags([Flags::default(), Flags::default()])
  ///   .with_ids([ExprId(2), ExprId(1)]);
  ///
  /// let db = Database::compile_multi_literal(&lit_set, Mode::BLOCK, None)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<(u32, &str)> = Vec::new();
  /// scratch
  ///   .scan_sync(
  ///     &db,
  ///     "he\0llo".into(),
  ///     |Match { id: ExpressionIndex(id), source, .. }| {
  ///       matches.push((id, unsafe { source.as_str() }));
  ///       MatchResult::Continue
  ///     })?;
  /// assert_eq!(&matches, &[(2, "he\0ll")]);
  ///
  /// matches.clear();
  /// scratch
  ///   .scan_sync(
  ///     &db,
  ///     "fr\0e\0edom".into(),
  ///     |Match { id: ExpressionIndex(id), source, .. }| {
  ///       matches.push((id, unsafe { source.as_str() }));
  ///       MatchResult::Continue
  ///     })?;
  /// assert_eq!(&matches, &[(1, "fr\0e\0e")]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn compile_multi_literal(
    literal_set: &LiteralSet,
    mode: Mode,
    platform: Option<&Platform>,
  ) -> Result<Self, VectorscanCompileError> {
    let mut db = ptr::null_mut();
    let mut compile_err = ptr::null_mut();
    let platform: Option<hs::hs_platform_info> = platform.cloned().map(Platform::into_native);
    VectorscanRuntimeError::copy_from_native_compile_error(
      unsafe {
        hs::hs_compile_lit_multi(
          literal_set.literals_ptr(),
          literal_set.flags_ptr(),
          literal_set.ids_ptr(),
          literal_set.lengths_ptr(),
          literal_set.num_elements(),
          mode.into_native(),
          platform
            .as_ref()
            .map(|p| p as *const hs::hs_platform_info)
            .unwrap_or(ptr::null()),
          &mut db,
          &mut compile_err,
        )
      },
      compile_err,
    )?;
    Ok(unsafe { Self::from_native(db) })
  }
}

/// # Introspection
/// These methods extract various bits of runtime information from the db.
impl Database {
  /// Return the size of the db allocation.
  ///
  /// Using [`Flags::UCP`] explodes the size of character classes, which
  /// increases the size of the state machine:
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::BLOCK)?;
  ///   let ascii_db = expr.compile(Flags::default(), Mode::BLOCK)?;
  ///
  ///   // Including UTF-8 classes increases the size:
  ///   assert!(utf8_db.database_size()? > ascii_db.database_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  ///
  /// This size corresponds to the requested allocation size passed to the db
  /// allocator:
  ///
  ///```
  /// #[cfg(all(feature = "alloc", feature = "compiler"))]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, alloc::*};
  ///   use std::alloc::System;
  ///
  ///   // Wrap the standard Rust System allocator.
  ///   let tracker = LayoutTracker::new(System.into());
  ///   // Register it as the allocator for databases.
  ///   assert!(set_db_allocator(tracker)?.is_none());
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::BLOCK)?;
  ///
  ///   // Get the database allocator we just registered and view its live allocations:
  ///   let allocs = get_db_allocator().as_ref().unwrap().current_allocations();
  ///   // Verify that only the single known db was allocated:
  ///   assert_eq!(1, allocs.len());
  ///   let (_p, layout) = allocs[0];
  ///
  ///   // Verify that the allocation size is the same as reported:
  ///   assert_eq!(layout.size(), utf8_db.database_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(all(feature = "alloc", feature = "compiler")))]
  /// # fn main() {}
  /// ```
  pub fn database_size(&self) -> Result<usize, VectorscanRuntimeError> {
    let mut ret: MaybeUninit<usize> = MaybeUninit::uninit();
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_database_size(self.as_ref_native(), ret.as_mut_ptr())
    })?;
    Ok(unsafe { ret.assume_init() })
  }

  /// Return the amount of space necessary to maintain stream state for this db.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let utf8_db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::STREAM)?;
  ///   let ascii_db = expr.compile(Flags::default(), Mode::STREAM)?;
  ///
  ///   // Including UTF-8 classes increases both db and stream size:
  ///   assert!(utf8_db.database_size()? > ascii_db.database_size()?);
  ///   assert!(utf8_db.stream_size()? > ascii_db.stream_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  ///
  /// This size corresponds to the requested allocation size passed to the
  /// stream allocator:
  ///
  ///```
  /// #[cfg(all(feature = "alloc", feature = "compiler"))]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, alloc::*, stream::*};
  ///   use std::alloc::System;
  ///
  ///   // Wrap the standard Rust System allocator.
  ///   let tracker = LayoutTracker::new(System.into());
  ///   // Register it as the allocator for streams.
  ///   assert!(set_stream_allocator(tracker)?.is_none());
  ///
  ///   let expr: Expression = r"\w".parse()?;
  ///   let db = expr.compile(Flags::UTF8 | Flags::UCP, Mode::STREAM)?;
  ///   let _stream = LiveStream::open(&db)?;
  ///
  ///   // Get the stream allocator we just registered and view its live allocations:
  ///   let allocs = get_stream_allocator().as_ref().unwrap().current_allocations();
  ///   // Verify that only the single known stream was allocated:
  ///   assert_eq!(1, allocs.len());
  ///   let (_p, layout) = allocs[0];
  ///
  ///   // Verify that the allocation size is the same as reported:
  ///   assert_eq!(layout.size(), db.stream_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(all(feature = "alloc", feature = "compiler")))]
  /// # fn main() {}
  /// ```
  #[cfg(feature = "stream")]
  #[cfg_attr(docsrs, doc(cfg(feature = "stream")))]
  pub fn stream_size(&self) -> Result<usize, VectorscanRuntimeError> {
    let mut ret: MaybeUninit<usize> = MaybeUninit::uninit();
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_stream_size(self.as_ref_native(), ret.as_mut_ptr())
    })?;
    Ok(unsafe { ret.assume_init() })
  }

  /// Extract metadata about the current database into a new string allocation.
  ///
  /// This is a convenience method that simply calls
  /// [`DbInfo::extract_db_info()`].
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let db = expr.compile(Flags::default(), Mode::BLOCK)?;
  ///   let info = db.info()?;
  ///   assert_eq!(info.as_str(), "Version: 5.4.11 Features: AVX2 Mode: BLOCK");
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn info(&self) -> Result<DbInfo, VectorscanRuntimeError> { DbInfo::extract_db_info(self) }
}

/// # Managing Allocations
/// These methods provide access to the underlying memory allocation containing
/// the data for the in-memory state machine. They can be used along with
/// [`SerializedDb::deserialize_db_at()`] to control the memory location used
/// for the state machine, or to preserve db allocations across weird lifetime
/// constraints.
///
/// Note that [`Self::database_size()`] can be used to determine the size of the
/// memory allocation pointed to by [`Self::as_ref_native()`] and
/// [`Self::as_mut_native()`].
impl Database {
  /// Wrap the provided allocation `p`.
  ///
  /// # Safety
  /// The pointer `p` must point to an initialized db allocation prepared by one
  /// of the compile or deserialize methods.
  ///
  /// This method also makes it especially easy to create multiple references to
  /// the same allocation, which will then cause a double free when
  /// [`Self::try_drop()`] is called more than once for the same db allocation.
  /// To avoid this, wrap the result in a [`ManuallyDrop`](mem::ManuallyDrop):
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, matchers::*, database::*, state::*};
  ///   use std::mem::ManuallyDrop;
  ///
  ///   // Compile a legitimate db:
  ///   let expr: Expression = "a+".parse()?;
  ///   let mut db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
  ///
  ///   // Create two new references to that allocation,
  ///   // wrapped to avoid calling the drop code:
  ///   let db_ptr: *mut NativeDb = db.as_mut_native();
  ///   let db_ref_1 = ManuallyDrop::new(unsafe { Database::from_native(db_ptr) });
  ///   let db_ref_2 = ManuallyDrop::new(unsafe { Database::from_native(db_ptr) });
  ///
  ///   // Both db references are valid and can be used for matching.
  ///   let mut scratch = Scratch::blank();
  ///   scratch.setup_for_db(&db_ref_1)?;
  ///   scratch.setup_for_db(&db_ref_2)?;
  ///
  ///   let mut matches: Vec<&str> = Vec::new();
  ///   scratch
  ///     .scan_sync(&db_ref_1, "aardvark".into(), |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   scratch
  ///     .scan_sync(&db_ref_2, "aardvark".into(), |Match { source, .. }| {
  ///       matches.push(unsafe { source.as_str() });
  ///       MatchResult::Continue
  ///     })?;
  ///   assert_eq!(&matches, &["a", "aa", "a", "a", "aa", "a"]);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub const unsafe fn from_native(p: *mut NativeDb) -> Self { Self(p) }

  /// Get a read-only reference to the db allocation.
  ///
  /// This method is mostly used internally and cast to a pointer to provide to
  /// the vectorscan native library methods.
  pub fn as_ref_native(&self) -> &NativeDb { unsafe { &*self.0 } }

  /// Get a mutable reference to the db allocation.
  ///
  /// The result of this method can be cast to a pointer and provided to
  /// [`Self::from_native()`].
  pub fn as_mut_native(&mut self) -> &mut NativeDb { unsafe { &mut *self.0 } }

  /// Free the underlying db allocation.
  ///
  /// # Safety
  /// This method must be called at most once over the lifetime of each db
  /// allocation. It is called by default on drop, so
  /// [`ManuallyDrop`](mem::ManuallyDrop) is recommended to wrap instances
  /// that reference external data in order to avoid attempting to free the
  /// referenced data.
  ///
  /// ## Only Frees Memory
  /// This method performs no processing other than freeing the allocated
  /// memory, so it can be skipped without leaking resources if the
  /// underlying [`NativeDb`] allocation is freed by some other means.
  pub unsafe fn try_drop(&mut self) -> Result<(), VectorscanRuntimeError> {
    VectorscanRuntimeError::from_native(unsafe { hs::hs_free_database(self.as_mut_native()) })
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

/// Wrappers over allocations from various sources.
///
/// In particular, this module contains [`DbAllocation`](alloc::DbAllocation),
/// which provides the logic needed to abstract over different sources of
/// backing data used to contain a [`SerializedDb`].
pub mod alloc {
  use std::{borrow::Cow, ops, slice};

  /// An allocation of memory using the misc allocator.
  ///
  /// The allocator used for this memory can be modified or accessed with
  /// [`crate::alloc::set_misc_allocator()`] and
  /// [`crate::alloc::get_misc_allocator()`] if the `"alloc"` feature is
  /// enabled.
  ///
  /// The backing memory will be deallocated by the misc allocator upon drop
  /// unless this is wrapped with a [`ManuallyDrop`](std::mem::ManuallyDrop).
  #[derive(Debug)]
  pub struct MiscAllocation {
    pub(crate) data: *mut u8,
    pub(crate) len: usize,
  }

  unsafe impl Send for MiscAllocation {}

  impl MiscAllocation {
    pub(crate) const fn as_ptr(&self) -> *mut u8 { self.data }

    pub(crate) const fn len(&self) -> usize { self.len }

    /// Return a view over the backing memory region.
    pub const fn as_slice(&self) -> &[u8] {
      unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
    }

    unsafe fn free(&mut self) { crate::free_misc(self.data) }
  }

  impl ops::Drop for MiscAllocation {
    fn drop(&mut self) {
      unsafe {
        self.free();
      }
    }
  }

  /// Wrapper over a misc or rust-level allocation.
  ///
  /// Used to provide [`super::SerializedDb`] with the ability to source data
  /// allocated by the vectorscan library itself or by other Rust code.
  #[derive(Debug)]
  pub enum DbAllocation<'a> {
    /// Memory was allocated with a `'static` lifetime using the registered misc
    /// allocator.
    Misc(MiscAllocation),
    /// Memory was allocated with a known lifetime and may be owned or
    /// referenced.
    Rust(Cow<'a, [u8]>),
  }

  /// Methods available to all types of allocations.
  impl<'a> DbAllocation<'a> {
    pub(crate) fn as_ptr(&self) -> *const u8 {
      match self {
        Self::Misc(misc) => misc.as_ptr(),
        Self::Rust(cow) => cow.as_ptr(),
      }
    }

    pub(crate) fn len(&self) -> usize {
      match self {
        Self::Misc(misc) => misc.len(),
        Self::Rust(cow) => cow.len(),
      }
    }

    /// Return a view over the backing memory region, wherever it may come from.
    pub fn as_slice(&self) -> &[u8] { unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) } }
  }

  /// Methods that produce new owned (`'static`) allocations.
  ///
  /// A [`Clone`] impl is also available for such owned allocations.
  impl DbAllocation<'static> {
    /// Copy the referenced data into a new Rust-level`'static` allocation.
    pub fn from_cloned_data(s: &DbAllocation) -> Self {
      let newly_allocated: Vec<u8> = s.as_slice().to_vec();
      Self::Rust(Cow::Owned(newly_allocated))
    }
  }

  impl Clone for DbAllocation<'static> {
    fn clone(&self) -> Self { Self::from_cloned_data(self) }
  }

  /// Wrappers over allocations performed by the chimera library.
  ///
  /// Since chimera does not support database deserialization like the base
  /// vectorscan library, there is no analogy to [`DbAllocation`].
  #[cfg(feature = "chimera")]
  #[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
  pub mod chimera {
    use std::{ops, slice};

    /// An allocation of memory using the chimera misc allocator.
    ///
    /// The allocator used for this memory can be modified or accessed with
    /// [`crate::alloc::chimera::set_chimera_misc_allocator()`] and
    /// [`crate::alloc::chimera::get_chimera_misc_allocator()`] if the `"alloc"`
    /// feature is enabled.
    ///
    /// The backing memory will be deallocated by the chimera misc allocator
    /// upon drop unless this is wrapped with a
    /// [`ManuallyDrop`](std::mem::ManuallyDrop).
    #[derive(Debug)]
    pub struct ChimeraMiscAllocation {
      pub(crate) data: *mut u8,
      pub(crate) len: usize,
    }

    unsafe impl Send for ChimeraMiscAllocation {}

    impl ChimeraMiscAllocation {
      pub(crate) const fn as_ptr(&self) -> *mut u8 { self.data }

      pub(crate) const fn len(&self) -> usize { self.len }

      /// Return a view over the backing memory region.
      pub const fn as_slice(&self) -> &[u8] {
        unsafe { slice::from_raw_parts(self.as_ptr(), self.len()) }
      }

      unsafe fn free(&mut self) { crate::free_misc_chimera(self.data) }
    }

    impl ops::Drop for ChimeraMiscAllocation {
      fn drop(&mut self) {
        unsafe {
          self.free();
        }
      }
    }
  }
}

/// Wrapper for allocated string data returned by [`Database::info()`].
#[repr(transparent)]
pub struct DbInfo(pub alloc::MiscAllocation);

impl DbInfo {
  const fn without_null(&self) -> impl slice::SliceIndex<[u8], Output=[u8]> { ..(self.0.len() - 1) }

  /// Return a view of the allocated string data.
  ///
  /// Vectorscan will always return valid UTF-8 data for this string, so it
  /// skips the validity check. Note that the returned string does not include
  /// the trailing null byte allocated by the underlying vectorscan library.
  pub fn as_str(&self) -> &str {
    unsafe { str::from_utf8_unchecked(&self.0.as_slice()[self.without_null()]) }
  }

  /// Write out metadata for `db` into a newly allocated region.
  pub fn extract_db_info(db: &Database) -> Result<Self, VectorscanRuntimeError> {
    let mut info = ptr::null_mut();
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_database_info(db.as_ref_native(), &mut info)
    })?;
    let len = unsafe { CStr::from_ptr(info) }.to_bytes_with_nul().len();
    assert!(len > 0);

    let ret = alloc::MiscAllocation {
      data: unsafe { mem::transmute(info) },
      len,
    };

    Ok(Self(ret))
  }
}

impl fmt::Debug for DbInfo {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "DbInfo({:?})", self.as_str()) }
}

impl fmt::Display for DbInfo {
  fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_str()) }
}

impl cmp::PartialEq for DbInfo {
  fn eq(&self, other: &Self) -> bool { self.as_str().eq(other.as_str()) }
}

impl cmp::Eq for DbInfo {}

impl cmp::PartialOrd for DbInfo {
  fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
}

impl cmp::Ord for DbInfo {
  fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_str().cmp(other.as_str()) }
}

impl hash::Hash for DbInfo {
  fn hash<H>(&self, state: &mut H)
  where H: hash::Hasher {
    self.as_str().hash(state);
  }
}

/// Wrapper for a serialized form of a [`Database`].
#[derive(Debug)]
#[repr(transparent)]
pub struct SerializedDb<'a>(
  /// This serialization data can be sourced from a variety of places.
  pub alloc::DbAllocation<'a>,
);

/// Methods available to all types of allocations.
impl<'a> SerializedDb<'a> {
  fn as_ptr(&self) -> *const c_char { unsafe { mem::transmute(self.0.as_ptr()) } }

  fn len(&self) -> usize { self.0.len() }

  /// Deserialize into a new db allocation.
  ///
  /// This will make a new allocation through the allocator from
  /// [`crate::alloc::set_db_allocator()`].
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let serialized_db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?.serialize()?;
  ///   let db = serialized_db.deserialize_db()?;
  ///
  ///   // Note that the expected deserialized size is the same
  ///   // as the resulting in-memory database size:
  ///   assert_eq!(db.database_size()?, serialized_db.deserialized_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn deserialize_db(&self) -> Result<Database, VectorscanRuntimeError> {
    let mut deserialized: MaybeUninit<*mut hs::hs_database> = MaybeUninit::uninit();
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_deserialize_database(self.as_ptr(), self.len(), deserialized.as_mut_ptr())
    })?;
    let deserialized = unsafe { deserialized.assume_init() };
    Ok(unsafe { Database::from_native(deserialized) })
  }

  /// Return the size of the allocation necessary for a subsequent call to
  /// [`Self::deserialize_db_at()`].
  pub fn deserialized_size(&self) -> Result<usize, VectorscanRuntimeError> {
    let mut deserialized_size: MaybeUninit<usize> = MaybeUninit::uninit();
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_serialized_database_size(self.as_ptr(), self.len(), deserialized_size.as_mut_ptr())
    })?;
    let deserialized_size = unsafe { deserialized_size.assume_init() };
    Ok(deserialized_size)
  }

  /// Like [`Self::deserialize_db()`], but points into an existing allocation
  /// instead of making a new allocation.
  ///
  /// # Safety
  /// `db` must point to an allocation at least
  /// [`Self::deserialized_size()`] bytes in size!
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*, database::*};
  ///   use std::mem;
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let serialized_db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?.serialize()?;
  ///
  ///   // Allocate a vector with sufficient capacity for the deserialized db:
  ///   let mut db_data: Vec<u8> = Vec::with_capacity(serialized_db.deserialized_size()?);
  ///   let db = unsafe {
  ///     let db_ptr: *mut NativeDb = mem::transmute(db_data.as_mut_ptr());
  ///     serialized_db.deserialize_db_at(db_ptr)?;
  ///     // Wrap in ManuallyDrop to avoid freeing memory owned by the `db_data` vector.
  ///     mem::ManuallyDrop::new(Database::from_native(db_ptr))
  ///   };
  ///   // Note that the expected deserialized size is the same
  ///   // as the resulting in-memory database size:
  ///   assert_eq!(db.database_size()?, serialized_db.deserialized_size()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub unsafe fn deserialize_db_at(&self, db: *mut NativeDb) -> Result<(), VectorscanRuntimeError> {
    VectorscanRuntimeError::from_native(hs::hs_deserialize_database_at(
      self.as_ptr(),
      self.len(),
      db,
    ))
  }

  /// Extract metadata about the serialized database into a new string
  /// allocation.
  ///
  ///```
  /// #[cfg(feature = "compiler")]
  /// fn main() -> Result<(), vectorscan::error::VectorscanError> {
  ///   use vectorscan::{expression::*, flags::*};
  ///
  ///   let expr: Expression = "a+".parse()?;
  ///   let serialized_db = expr.compile(Flags::default(), Mode::BLOCK)?.serialize()?;
  ///   let info = serialized_db.extract_db_info()?;
  ///   assert_eq!(info.as_str(), "Version: 5.4.11 Features: AVX2 Mode: BLOCK");
  ///   // Info is the same as would have been provided from deserializing:
  ///   assert_eq!(info, serialized_db.deserialize_db()?.info()?);
  ///   Ok(())
  /// }
  /// # #[cfg(not(feature = "compiler"))]
  /// # fn main() {}
  /// ```
  pub fn extract_db_info(&self) -> Result<DbInfo, VectorscanRuntimeError> {
    let mut info = ptr::null_mut();
    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_serialized_database_info(self.as_ptr(), self.len(), &mut info)
    })?;
    let len = unsafe { CStr::from_ptr(info) }.to_bytes_with_nul().len();
    assert!(len > 0);

    let ret = alloc::MiscAllocation {
      data: info as *mut u8,
      len,
    };

    Ok(DbInfo(ret))
  }
}

/// # Owned Allocations
/// Methods that produce new owned (`'static`) allocations.
///
/// A [`Clone`] impl is also available for such owned allocations.
impl SerializedDb<'static> {
  /// Write a serialized representation of `db` into a newly allocated region of
  /// memory.
  pub fn serialize_db(db: &Database) -> Result<Self, VectorscanRuntimeError> {
    let mut data = ptr::null_mut();
    let mut len: usize = 0;

    VectorscanRuntimeError::from_native(unsafe {
      hs::hs_serialize_database(db.as_ref_native(), &mut data, &mut len)
    })?;

    let data = data as *mut u8;

    Ok(Self(alloc::DbAllocation::Misc(alloc::MiscAllocation {
      data,
      len,
    })))
  }

  /// Allocate a new region of memory and copy over the referenced data from
  /// `s`.
  pub fn from_cloned_data(s: &SerializedDb) -> Self {
    let SerializedDb(ref s) = s;
    Self(alloc::DbAllocation::from_cloned_data(s))
  }
}

impl Clone for SerializedDb<'static> {
  fn clone(&self) -> Self { Self::from_cloned_data(self) }
}

/// Compile chimera state machines from expressions.
///
/// Unlike the base vectorscan library, chimera does not support database
/// serialization, so new [`chimera::ChimeraDb`] instances can only be created
/// by compiling them. That is why the `"chimera"` feature for this crate
/// requires the `"compiler"` feature.
#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::alloc::chimera::ChimeraMiscAllocation;
  #[cfg(feature = "compiler")]
  use super::Platform;
  #[cfg(feature = "compiler")]
  use crate::{
    error::chimera::ChimeraCompileError,
    expression::chimera::{ChimeraExpression, ChimeraExpressionSet, ChimeraMatchLimits},
    flags::chimera::{ChimeraFlags, ChimeraMode},
  };
  use crate::{error::chimera::ChimeraRuntimeError, hs, state::chimera::ChimeraScratch};

  use std::{cmp, ffi::CStr, fmt, hash, mem, ops, ptr, slice, str};

  /// Pointer type for chimera db allocations used in [`ChimeraDb#Managing
  /// Allocations`](ChimeraDb#managing-allocations).
  pub type NativeChimeraDb = hs::ch_database;

  /// Read-only description of an in-memory PCRE state machine.
  ///
  /// This type also serves as the entry point to the various types of [pattern
  /// compilers](#pattern-compilers), including single expressions and
  /// expression sets.
  #[derive(Debug)]
  #[repr(transparent)]
  pub struct ChimeraDb(*mut NativeChimeraDb);

  /// # Convenience Methods
  /// These methods prepare some resource within a new heap allocation and are
  /// useful for doctests and examples.
  ///
  /// ## Scratch Setup
  /// Databases already require their own heap allocation, which can be managed
  /// with the methods in [Managing Allocations](#managing-allocations).
  /// However, databases also impose a sort of implicit dynamic lifetime
  /// constraint on [`ChimeraScratch`] objects, which must be initialized
  /// against a db with [`ChimeraScratch::setup_for_db()`] before vectorscan
  /// can do any searching.
  ///
  /// It is encouraged to re-use [`ChimeraScratch`] objects across databases
  /// where possible to minimize unnecessary allocations, but
  /// [`Self::allocate_scratch()`] is provided as a convenience method to
  /// quickly produce a 1:1 db:scratch mapping.
  impl ChimeraDb {
    /// Call [`ChimeraScratch::setup_for_db()`] on a newly allocated
    /// [`ChimeraScratch::blank()`].
    ///
    ///```
    /// # fn main() -> Result<(), vectorscan::error::chimera::ChimeraError> {
    /// use vectorscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*};
    ///
    /// let expr: ChimeraExpression = "a+".parse()?;
    /// let db = expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// let mut matches: Vec<&str> = Vec::new();
    /// let e = |_| ChimeraMatchResult::Continue;
    /// scratch
    ///   .scan_sync(&db, "aardvark".into(), |ChimeraMatch { source, .. }| {
    ///     matches.push(unsafe { source.as_str() });
    ///     ChimeraMatchResult::Continue
    ///   }, e)?;
    /// assert_eq!(&matches, &["aa", "a"]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn allocate_scratch(&self) -> Result<ChimeraScratch, ChimeraRuntimeError> {
      let mut scratch = ChimeraScratch::blank();
      scratch.setup_for_db(self)?;
      Ok(scratch)
    }
  }

  /// # Pattern Compilers
  /// Chimera supports compiling state machines for single PCRE pattern strings
  /// as well as parallel sets of those patterns. Each compile method currently
  /// supports all [`ChimeraFlags`] arguments.
  ///
  /// ## Platform Compatibility
  /// Each method also accepts an optional [`Platform`] object,
  /// which is used to select processor features to compile the database for.
  /// While the default of [`None`] will enable all features available to the
  /// current processor, some features can be disabled in order to produce a
  /// database which can execute on a wider variety of target platforms.
  /// **However, note that since chimera does not support deserialization like
  /// the base vectorscan library, there currently seems to be no real benefit
  /// to a more-generic but less-performant compiled database, so using
  /// [`None`] is recommended in all cases.**
  ///
  ///```
  /// # fn main() -> Result<(), vectorscan::error::chimera::ChimeraError> {
  /// use vectorscan::{expression::chimera::*, flags::{*, chimera::*, platform::*}, database::chimera::*};
  ///
  /// let expr: ChimeraExpression = "a+".parse()?;
  ///
  /// // Verify that the current platform has AVX2 instructions, and make a db:
  /// let plat = Platform::local()?;
  /// assert!(plat.cpu_features.contains(&CpuFeatures::AVX2));
  /// assert!(plat != Platform::GENERIC);
  /// let db_with_avx2 = ChimeraDb::compile(
  ///   &expr,
  ///   ChimeraFlags::default(),
  ///   ChimeraMode::NOGROUPS,
  ///   Some(&plat),
  /// )?;
  ///
  /// // The only specialized instructions we have available are AVX2:
  /// assert_eq!(CpuFeatures::NONE, plat.cpu_features & !CpuFeatures::AVX2);
  /// // Avoid using AVX2 instructions:
  /// let db_no_avx2 = ChimeraDb::compile(
  ///   &expr,
  ///   ChimeraFlags::default(),
  ///   ChimeraMode::NOGROUPS,
  ///   Some(&Platform::GENERIC),
  /// )?;
  ///
  /// // Instruction selection does not affect the size of the state machine:
  /// assert!(db_with_avx2.database_size()? == db_no_avx2.database_size()?);
  ///
  /// // Now create a db with None for the platform:
  /// let db_local = ChimeraDb::compile(
  ///   &expr,
  ///   ChimeraFlags::default(),
  ///   ChimeraMode::NOGROUPS,
  ///   None,
  /// )?;
  /// assert!(db_with_avx2.database_size()? == db_local.database_size()?);
  ///
  /// // Using None produces the same type of db as Platform::local():
  /// assert!(db_with_avx2.info()? == db_local.info()?);
  /// assert!(db_no_avx2.info()? != db_local.info()?);
  /// # Ok(())
  /// # }
  /// ```
  ///
  /// ## Dynamic Memory Allocation
  /// These methods allocate a new region of memory using the db allocator
  /// (which can be overridden with
  /// [`crate::alloc::chimera::set_chimera_db_allocator()`]). That allocation
  /// can be manipulated as described in [Managing Allocations](#
  /// managing-allocations).
  #[cfg(feature = "compiler")]
  #[cfg_attr(docsrs, doc(cfg(feature = "compiler")))]
  impl ChimeraDb {
    /// Single pattern compiler.
    ///
    /// # Accepted Flags
    /// - [`CASELESS`](ChimeraFlags::CASELESS)
    /// - [`DOTALL`](ChimeraFlags::DOTALL)
    /// - [`MULTILINE`](ChimeraFlags::MULTILINE)
    /// - [`SINGLEMATCH`](ChimeraFlags::SINGLEMATCH)
    /// - [`UTF8`](ChimeraFlags::UTF8)
    /// - [`UCP`](ChimeraFlags::UCP)
    ///
    ///```
    /// # fn main() -> Result<(), vectorscan::error::chimera::ChimeraError> {
    /// use vectorscan::{expression::chimera::*, flags::chimera::*, database::chimera::*, matchers::chimera::*};
    ///
    /// let expr: ChimeraExpression = "hell(o)?".parse()?;
    /// let db = ChimeraDb::compile(&expr, ChimeraFlags::default(), ChimeraMode::GROUPS, None)?;
    ///
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// let mut matches: Vec<(&str, Option<&str>)> = Vec::new();
    /// let e = |_| ChimeraMatchResult::Continue;
    /// scratch
    ///   .scan_sync(&db, "hello".into(), |m| {
    ///     matches.push(unsafe { (
    ///       m.source.as_str(),
    ///       m.captures.unwrap()[1].map(|c| c.as_str()),
    ///     ) });
    ///     ChimeraMatchResult::Continue
    ///   }, e)?;
    /// assert_eq!(&matches, &[("hello", Some("o"))]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn compile(
      expression: &ChimeraExpression,
      flags: ChimeraFlags,
      mode: ChimeraMode,
      platform: Option<&Platform>,
    ) -> Result<Self, ChimeraCompileError> {
      let mut db = ptr::null_mut();
      let mut compile_err = ptr::null_mut();
      let platform: Option<hs::hs_platform_info> = platform.cloned().map(Platform::into_native);
      ChimeraRuntimeError::copy_from_native_compile_error(
        unsafe {
          hs::ch_compile(
            expression.as_ptr(),
            flags.into_native(),
            mode.into_native(),
            platform
              .as_ref()
              .map(|p| p as *const hs::hs_platform_info)
              .unwrap_or(ptr::null()),
            &mut db,
            &mut compile_err,
          )
        },
        compile_err,
      )?;
      Ok(unsafe { Self::from_native(db) })
    }

    /// Multiple pattern compiler.
    ///
    /// # Accepted Flags
    /// - [`CASELESS`](ChimeraFlags::CASELESS)
    /// - [`DOTALL`](ChimeraFlags::DOTALL)
    /// - [`MULTILINE`](ChimeraFlags::MULTILINE)
    /// - [`SINGLEMATCH`](ChimeraFlags::SINGLEMATCH)
    /// - [`UTF8`](ChimeraFlags::UTF8)
    /// - [`UCP`](ChimeraFlags::UCP)
    ///
    ///```
    /// # fn main() -> Result<(), vectorscan::error::chimera::ChimeraError> {
    /// use vectorscan::{expression::{*, chimera::*}, flags::chimera::*, database::chimera::*, matchers::chimera::*};
    ///
    /// let a_expr: ChimeraExpression = "a+".parse()?;
    /// let b_expr: ChimeraExpression = "b+".parse()?;
    /// let exprs = ChimeraExpressionSet::from_exprs([&a_expr, &b_expr])
    ///   .with_ids([ExprId(1), ExprId(2)])
    ///   .with_limits(ChimeraMatchLimits { match_limit: 30, match_limit_recursion: 30 });
    /// let db = ChimeraDb::compile_multi(&exprs, ChimeraMode::NOGROUPS, None)?;
    /// let mut scratch = db.allocate_scratch()?;
    ///
    /// let mut matches: Vec<&str> = Vec::new();
    /// let e = |_| ChimeraMatchResult::Continue;
    /// scratch.scan_sync(&db, "aardvark imbibbe".into(), |ChimeraMatch { source, .. }| {
    ///    matches.push(unsafe { source.as_str() });
    ///    ChimeraMatchResult::Continue
    ///  }, e)?;
    /// assert_eq!(&matches, &["aa", "a", "b", "bb"]);
    /// # Ok(())
    /// # }
    /// ```
    pub fn compile_multi(
      exprs: &ChimeraExpressionSet,
      mode: ChimeraMode,
      platform: Option<&Platform>,
    ) -> Result<Self, ChimeraCompileError> {
      let mut db = ptr::null_mut();
      let mut compile_err = ptr::null_mut();
      let platform: Option<hs::hs_platform_info> = platform.cloned().map(Platform::into_native);
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
              platform
                .as_ref()
                .map(|p| p as *const hs::hs_platform_info)
                .unwrap_or(ptr::null()),
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
              platform
                .as_ref()
                .map(|p| p as *const hs::hs_platform_info)
                .unwrap_or(ptr::null()),
              &mut db,
              &mut compile_err,
            )
          }
        },
        compile_err,
      )?;
      Ok(unsafe { Self::from_native(db) })
    }
  }

  /// # Introspection
  /// These methods extract various bits of runtime information from the db.
  impl ChimeraDb {
    /// Return the size of the db allocation.
    ///
    /// Using [`ChimeraFlags::UCP`] explodes the size of character classes,
    /// which increases the size of the state machine:
    ///
    ///```
    /// # fn main() -> Result<(), vectorscan::error::chimera::ChimeraError> {
    /// use vectorscan::{expression::chimera::*, flags::chimera::*};
    ///
    /// let expr: ChimeraExpression = r"\w".parse()?;
    /// let utf8_db = expr.compile(
    ///   ChimeraFlags::UTF8 | ChimeraFlags::UCP,
    ///   ChimeraMode::NOGROUPS,
    /// )?;
    /// let ascii_db = expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
    ///
    /// // Including UTF-8 classes increases the size:
    /// assert!(utf8_db.database_size()? > ascii_db.database_size()?);
    /// # Ok(())
    /// # }
    /// ```
    ///
    /// This size corresponds to the requested allocation size passed to the db
    /// allocator:
    ///
    ///```
    /// #[cfg(feature = "alloc")]
    /// fn main() -> Result<(), vectorscan::error::chimera::ChimeraError> {
    ///   use vectorscan::{expression::chimera::*, flags::chimera::*, alloc::{*, chimera::*}};
    ///   use std::alloc::System;
    ///
    ///   // Wrap the standard Rust System allocator.
    ///   let tracker = LayoutTracker::new(System.into());
    ///   // Register it as the allocator for databases.
    ///   assert!(set_chimera_db_allocator(tracker)?.is_none());
    ///
    ///   let expr: ChimeraExpression = r"\w".parse()?;
    ///   let utf8_db = expr.compile(
    ///     ChimeraFlags::UTF8 | ChimeraFlags::UCP,
    ///     ChimeraMode::NOGROUPS,
    ///   )?;
    ///
    ///   // Get the database allocator we just registered and view its live allocations:
    ///   let allocs = get_chimera_db_allocator().as_ref().unwrap().current_allocations();
    ///   // Verify that only the single known db was allocated:
    ///   assert_eq!(1, allocs.len());
    ///   let (_p, layout) = allocs[0];
    ///
    ///   // Verify that the allocation size is the same as reported:
    ///   assert_eq!(layout.size(), utf8_db.database_size()?);
    ///   Ok(())
    /// }
    /// # #[cfg(not(feature = "alloc"))]
    /// # fn main() {}
    /// ```
    pub fn database_size(&self) -> Result<usize, ChimeraRuntimeError> {
      let mut database_size: usize = 0;
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_database_size(self.as_ref_native(), &mut database_size)
      })?;
      Ok(database_size)
    }

    /// Extract metadata about the current database into a new string
    /// allocation.
    ///
    /// This is a convenience method that simply calls
    /// [`ChimeraDbInfo::extract_db_info()`].
    ///
    ///```
    /// # fn main() -> Result<(), vectorscan::error::chimera::ChimeraError> {
    /// use vectorscan::{expression::chimera::*, flags::chimera::*, database::chimera::*};
    ///
    /// let expr: ChimeraExpression = "a+".parse()?;
    /// let db = expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
    /// let info = ChimeraDbInfo::extract_db_info(&db)?;
    /// assert_eq!(info.as_str(), "Chimera Version: 5.4.11 Features: AVX2 Mode: BLOCK");
    /// # Ok(())
    /// # }
    /// ```
    pub fn info(&self) -> Result<ChimeraDbInfo, ChimeraRuntimeError> {
      ChimeraDbInfo::extract_db_info(self)
    }
  }

  /// # Managing Allocations
  /// These methods provide access to the underlying memory allocation
  /// containing the data for the in-memory state machine. They can be used to
  /// control the memory location used for the state machine, or to preserve
  /// db allocations across weird lifetime constraints.
  ///
  /// Note that [`Self::database_size()`] can be used to determine the size of
  /// the memory allocation pointed to by [`Self::as_ref_native()`] and
  /// [`Self::as_mut_native()`].
  impl ChimeraDb {
    /// Wrap the provided allocation `p`.
    ///
    /// # Safety
    /// The pointer `p` must point to an initialized db allocation prepared by
    /// one of the compile methods.
    ///
    /// This method also makes it especially easy to create multiple references
    /// to the same allocation, which will then cause a double free when
    /// [`Self::try_drop()`] is called more than once for the same db
    /// allocation. To avoid this, wrap the result in a
    /// [`ManuallyDrop`](mem::ManuallyDrop):
    ///
    ///```
    /// # fn main() -> Result<(), vectorscan::error::chimera::ChimeraError> {
    /// use vectorscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*, database::chimera::*, state::chimera::*};
    /// use std::mem::ManuallyDrop;
    ///
    /// // Compile a legitimate db:
    /// let expr: ChimeraExpression = "a+".parse()?;
    /// let mut db = expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
    ///
    /// // Create two new references to that allocation,
    /// // wrapped to avoid calling the drop code:
    /// let db_ptr: *mut NativeChimeraDb = db.as_mut_native();
    /// let db_ref_1 = ManuallyDrop::new(unsafe { ChimeraDb::from_native(db_ptr) });
    /// let db_ref_2 = ManuallyDrop::new(unsafe { ChimeraDb::from_native(db_ptr) });
    ///
    /// // Both db references are valid and can be used for matching.
    /// let mut scratch = ChimeraScratch::blank();
    /// scratch.setup_for_db(&db_ref_1)?;
    /// scratch.setup_for_db(&db_ref_2)?;
    ///
    /// let mut matches: Vec<&str> = Vec::new();
    /// let e = |_| ChimeraMatchResult::Continue;
    /// scratch
    ///   .scan_sync(&db_ref_1, "aardvark".into(), |ChimeraMatch { source, .. }| {
    ///     matches.push(unsafe { source.as_str() });
    ///     ChimeraMatchResult::Continue
    ///   }, e)?;
    /// scratch
    ///   .scan_sync(&db_ref_2, "aardvark".into(), |ChimeraMatch { source, .. }| {
    ///     matches.push(unsafe { source.as_str() });
    ///     ChimeraMatchResult::Continue
    ///   }, e)?;
    /// assert_eq!(&matches, &["aa", "a", "aa", "a"]);
    /// # Ok(())
    /// # }
    /// ```
    pub const unsafe fn from_native(p: *mut NativeChimeraDb) -> Self { Self(p) }

    /// Get a read-only reference to the db allocation.
    ///
    /// This method is mostly used internally and cast to a pointer to provide
    /// to the chimera native library methods.
    pub fn as_ref_native(&self) -> &NativeChimeraDb { unsafe { &*self.0 } }

    /// Get a mutable reference to the db allocation.
    ///
    /// The result of this method can be cast to a pointer and provided to
    /// [`Self::from_native()`].
    pub fn as_mut_native(&mut self) -> &mut NativeChimeraDb { unsafe { &mut *self.0 } }

    /// Free the underlying db allocation.
    ///
    /// # Safety
    /// This method must be called at most once over the lifetime of each db
    /// allocation. It is called by default on drop, so
    /// [`ManuallyDrop`](mem::ManuallyDrop) is recommended to wrap instances
    /// that reference external data in order to avoid attempting to free the
    /// referenced data.
    ///
    /// ## Only Frees Memory
    /// This method performs no processing other than freeing the allocated
    /// memory, so it can be skipped without leaking resources if the
    /// underlying [`NativeChimeraDb`] allocation is freed by some other means.
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

  /// Wrapper for allocated string data returned by [`ChimeraDb::info()`].
  pub struct ChimeraDbInfo(ChimeraMiscAllocation);

  impl ChimeraDbInfo {
    const fn without_null(&self) -> impl slice::SliceIndex<[u8], Output=[u8]> {
      ..(self.0.len() - 1)
    }

    /// Return a view of the allocated string data.
    ///
    /// Chimera will always return valid UTF-8 data for this string, so it skips
    /// the validity check. Note that the returned string does not include
    /// the trailing null byte allocated by the underlying chimera library.
    pub fn as_str(&self) -> &str {
      unsafe { str::from_utf8_unchecked(&self.0.as_slice()[self.without_null()]) }
    }

    /// Write out metadata for `db` into a newly allocated region.
    pub fn extract_db_info(db: &ChimeraDb) -> Result<Self, ChimeraRuntimeError> {
      let mut info = ptr::null_mut();
      ChimeraRuntimeError::from_native(unsafe {
        hs::ch_database_info(db.as_ref_native(), &mut info)
      })?;
      let len = unsafe { CStr::from_ptr(info) }.to_bytes_with_nul().len();
      assert!(len > 0);

      let ret = ChimeraMiscAllocation {
        data: unsafe { mem::transmute(info) },
        len,
      };

      Ok(Self(ret))
    }
  }

  impl fmt::Debug for ChimeraDbInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
      write!(f, "ChimeraDbInfo({:?})", self.as_str())
    }
  }

  impl fmt::Display for ChimeraDbInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result { write!(f, "{}", self.as_str()) }
  }

  impl cmp::PartialEq for ChimeraDbInfo {
    fn eq(&self, other: &Self) -> bool { self.as_str().eq(other.as_str()) }
  }

  impl cmp::Eq for ChimeraDbInfo {}

  impl cmp::PartialOrd for ChimeraDbInfo {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> { Some(self.cmp(other)) }
  }

  impl cmp::Ord for ChimeraDbInfo {
    fn cmp(&self, other: &Self) -> cmp::Ordering { self.as_str().cmp(other.as_str()) }
  }

  impl hash::Hash for ChimeraDbInfo {
    fn hash<H>(&self, state: &mut H)
    where H: hash::Hasher {
      self.as_str().hash(state);
    }
  }
}
