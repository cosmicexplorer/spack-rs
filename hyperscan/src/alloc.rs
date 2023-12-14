/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Routines for overriding the allocators used in several components of
//! hyperscan.
//!
//! These methods mutate global process state when setting function pointers for
//! alloc and free, so this module requires the `"alloc"` feature, which itself
//! requires the `"static"` feature which statically links the hyperscan native
//! library to ensure exclusive access to this global state.

use crate::{error::HyperscanRuntimeError, hs};

use indexmap::IndexMap;
use libc;
use parking_lot::{Mutex, RwLock};

use std::{
  alloc::{GlobalAlloc, Layout},
  mem, ops,
  os::raw::c_void,
  ptr::{self, NonNull},
  sync::Arc,
};

pub trait MallocLikeAllocator {
  fn allocate(&self, size: usize) -> Option<NonNull<u8>>;
  fn deallocate(&self, ptr: NonNull<u8>);
}

pub struct LayoutTracker {
  allocator: Arc<dyn GlobalAlloc>,
  layouts: Mutex<IndexMap<NonNull<u8>, Layout>>,
}

unsafe impl Send for LayoutTracker {}
unsafe impl Sync for LayoutTracker {}

impl ops::Drop for LayoutTracker {
  fn drop(&mut self) {
    if !self.layouts.get_mut().is_empty() {
      unreachable!("can't drop LayoutTracker with pending allocations as this would leak memory");
    }
  }
}

impl LayoutTracker {
  pub fn new(allocator: Arc<impl GlobalAlloc+'static>) -> Self {
    Self {
      allocator,
      layouts: Mutex::new(IndexMap::new()),
    }
  }

  pub fn current_allocations(&mut self) -> Vec<(NonNull<u8>, Layout)> {
    self
      .layouts
      .get_mut()
      .iter()
      .map(|(x, y)| (*x, *y))
      .collect()
  }
}

impl MallocLikeAllocator for LayoutTracker {
  fn allocate(&self, size: usize) -> Option<NonNull<u8>> {
    /* .alloc() is undefined when provided a 0 size alloc, so handle it here. */
    if size == 0 {
      return None;
    }
    /* NB: Allocate everything with 8-byte alignment. Only the database allocator
     * is documented to require 8-byte alignment; nothing else seems to break
     * if we use it for everything! */
    let layout = Layout::from_size_align(size, 8).unwrap();
    /* This is part of the safety guarantee imposed by .alloc(): */
    assert!(layout.size() > 0);
    let ret = NonNull::new(unsafe { self.allocator.alloc(layout) })?;
    assert!(self.layouts.lock().insert(ret, layout).is_none());
    Some(ret)
  }

  fn deallocate(&self, ptr: NonNull<u8>) {
    let layout = self.layouts.lock().remove(&ptr).unwrap();
    unsafe {
      self.allocator.dealloc(ptr.as_ptr(), layout);
    }
  }
}

unsafe fn alloc_or_libc_fallback(
  allocator: &RwLock<Option<LayoutTracker>>,
  size: usize,
) -> *mut c_void {
  match allocator.read().as_ref() {
    Some(allocator) => allocator
      .allocate(size)
      .map(|p| mem::transmute(p.as_ptr()))
      .unwrap_or(ptr::null_mut()),
    None => libc::malloc(size),
  }
}

unsafe fn dealloc_or_libc_fallback(allocator: &RwLock<Option<LayoutTracker>>, p: *mut c_void) {
  match allocator.read().as_ref() {
    Some(allocator) => {
      if let Some(p) = NonNull::new(p as *mut u8) {
        allocator.deallocate(p);
      }
    },
    None => libc::free(p),
  }
}

macro_rules! allocator {
  ($lock_name:ident, $alloc_name:ident, $free_name:ident) => {
    static $lock_name: RwLock<Option<LayoutTracker>> = RwLock::new(None);

    pub(crate) unsafe extern "C" fn $alloc_name(size: usize) -> *mut c_void {
      alloc_or_libc_fallback(&$lock_name, size)
    }

    pub(crate) unsafe extern "C" fn $free_name(p: *mut c_void) {
      dealloc_or_libc_fallback(&$lock_name, p)
    }
  };
}

allocator![DB_ALLOCATOR, db_alloc_func, db_free_func];

///```
/// #[cfg(feature = "compiler")]
/// fn main() -> Result<(), hyperscan::error::HyperscanError> {
///   use hyperscan::{expression::*, flags::*, database::*, matchers::*, alloc::*};
///   use std::{alloc::System, mem::ManuallyDrop};
///
///   // Set the process-global allocator to use for Database instances:
///   let tracker = LayoutTracker::new(System.into());
///   // There was no custom allocator registered yet.
///   assert!(set_db_allocator(tracker).unwrap().is_none());
///
///   let expr: Expression = "asdf".parse()?;
///   // Use ManuallyDrop to avoid calling the hyperscan db free method,
///   // since we will be invalidating the pointer by changing the allocator,
///   // and the .try_drop() method and Drop impl both call into
///   // whatever allocator is currently active to free the pointer, which will error.
///   let mut db = ManuallyDrop::new(expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?);
///
///   // Change the allocator to a fresh LayoutTracker:
///   let mut tracker = set_db_allocator(LayoutTracker::new(System.into())).unwrap().unwrap();
///   // Get the extant allocations from the old LayoutTracker:
///   let allocs = tracker.current_allocations();
///   // Verify that only the single known db was allocated:
///   assert_eq!(1, allocs.len());
///   let (p, layout) = allocs[0];
///   let db_ptr: *mut NativeDb = db.as_mut_native();
///   assert_eq!(p.as_ptr() as *mut NativeDb, db_ptr);
///
///   // Despite having reset the allocator, our previous db is still valid
///   // and can be used for matching:
///   let mut scratch = db.allocate_scratch()?;
///   let mut matches: Vec<&str> = Vec::new();
///   scratch.scan_sync(&db, "asdf asdf".into(), |m| {
///     matches.push(unsafe { m.source.as_str() });
///     MatchResult::Continue
///   })?;
///   assert_eq!(&matches, &["asdf", "asdf"]);
///
///   // We can deserialize something from somewhere else into the db handle:
///   let expr: Literal = "hello".parse()?;
///   let serialized_db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?.serialize()?;
///   // Ensure the allocated database is large enough to contain the deserialized one:
///   assert!(layout.size() >= serialized_db.deserialized_size()?);
///   // NB: overwrite the old database!
///   unsafe { serialized_db.deserialize_db_at(db.as_mut_native())?; }
///
///   // Reuse the same database object now:
///   scratch.setup_for_db(&db)?;
///   matches.clear();
///   scratch.scan_sync(&db, "hello hello".into(), |m| {
///     matches.push(unsafe { m.source.as_str() });
///     MatchResult::Continue
///   })?;
///   assert_eq!(&matches, &["hello", "hello"]);
///
///   // Need to deallocate the db by hand in order to drop the original LayoutTracker
///   // without panicking:
///   tracker.deallocate(p);
///   // NB: `db` is now INVALID and points to FREED MEMORY!!!
///   Ok(())
/// }
/// # #[cfg(not(feature = "compiler"))]
/// # fn main() {}
/// ```
pub fn set_db_allocator(
  tracker: LayoutTracker,
) -> Result<Option<LayoutTracker>, HyperscanRuntimeError> {
  let ret = DB_ALLOCATOR.write().replace(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_database_allocator(Some(db_alloc_func), Some(db_free_func))
  })?;
  Ok(ret)
}

allocator![MISC_ALLOCATOR, misc_alloc_func, misc_free_func];

pub fn set_misc_allocator(
  tracker: LayoutTracker,
) -> Result<Option<LayoutTracker>, HyperscanRuntimeError> {
  let ret = MISC_ALLOCATOR.write().replace(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_misc_allocator(Some(misc_alloc_func), Some(misc_free_func))
  })?;
  Ok(ret)
}

allocator![SCRATCH_ALLOCATOR, scratch_alloc_func, scratch_free_func];

pub fn set_scratch_allocator(
  tracker: LayoutTracker,
) -> Result<Option<LayoutTracker>, HyperscanRuntimeError> {
  let ret = SCRATCH_ALLOCATOR.write().replace(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_scratch_allocator(Some(scratch_alloc_func), Some(scratch_free_func))
  })?;
  Ok(ret)
}

allocator![STREAM_ALLOCATOR, stream_alloc_func, stream_free_func];

pub fn set_stream_allocator(
  tracker: LayoutTracker,
) -> Result<Option<LayoutTracker>, HyperscanRuntimeError> {
  let ret = STREAM_ALLOCATOR.write().replace(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_stream_allocator(Some(stream_alloc_func), Some(stream_free_func))
  })?;
  Ok(ret)
}

///```
/// #[cfg(feature = "compiler")]
/// fn main() -> Result<(), hyperscan::error::HyperscanError> {
///   use hyperscan::{expression::*, flags::*, matchers::*};
///   use std::alloc::System;
///
///   hyperscan::alloc::set_allocator(System.into())?;
///
///   let expr: Expression = "(he)ll".parse()?;
///   let db = expr.compile(Flags::UTF8, Mode::BLOCK)?;
///
///   let mut scratch = db.allocate_scratch()?;
///
///   let mut matches: Vec<&str> = Vec::new();
///   scratch
///     .scan_sync(&db, "hello".into(), |m| {
///       matches.push(unsafe { m.source.as_str() });
///       MatchResult::Continue
///     })?;
///   assert_eq!(&matches, &["hell"]);
///   Ok(())
/// }
/// # #[cfg(not(feature = "compiler"))]
/// # fn main() {}
/// ```
pub fn set_allocator(
  allocator: Arc<impl GlobalAlloc+'static>,
) -> Result<(), HyperscanRuntimeError> {
  for f in [
    set_db_allocator,
    set_misc_allocator,
    set_scratch_allocator,
    set_stream_allocator,
  ]
  .into_iter()
  {
    f(LayoutTracker::new(allocator.clone()))?;
  }
  Ok(())
}

#[cfg(feature = "chimera")]
#[cfg_attr(docsrs, doc(cfg(feature = "chimera")))]
pub mod chimera {
  use super::*;
  use crate::error::chimera::*;

  allocator![
    CHIMERA_DB_ALLOCATOR,
    chimera_db_alloc_func,
    chimera_db_free_func
  ];

  pub fn set_chimera_db_allocator(
    tracker: LayoutTracker,
  ) -> Result<Option<LayoutTracker>, ChimeraRuntimeError> {
    let ret = CHIMERA_DB_ALLOCATOR.write().replace(tracker);
    ChimeraRuntimeError::from_native(unsafe {
      hs::ch_set_database_allocator(Some(chimera_db_alloc_func), Some(chimera_db_free_func))
    })?;
    Ok(ret)
  }

  allocator![
    CHIMERA_MISC_ALLOCATOR,
    chimera_misc_alloc_func,
    chimera_misc_free_func
  ];

  pub fn set_chimera_misc_allocator(
    tracker: LayoutTracker,
  ) -> Result<Option<LayoutTracker>, ChimeraRuntimeError> {
    let ret = CHIMERA_MISC_ALLOCATOR.write().replace(tracker);
    ChimeraRuntimeError::from_native(unsafe {
      hs::ch_set_misc_allocator(Some(chimera_misc_alloc_func), Some(chimera_misc_free_func))
    })?;
    Ok(ret)
  }

  allocator![
    CHIMERA_SCRATCH_ALLOCATOR,
    chimera_scratch_alloc_func,
    chimera_scratch_free_func
  ];

  pub fn set_chimera_scratch_allocator(
    tracker: LayoutTracker,
  ) -> Result<Option<LayoutTracker>, ChimeraRuntimeError> {
    let ret = CHIMERA_SCRATCH_ALLOCATOR.write().replace(tracker);
    ChimeraRuntimeError::from_native(unsafe {
      hs::ch_set_scratch_allocator(
        Some(chimera_scratch_alloc_func),
        Some(chimera_scratch_free_func),
      )
    })?;
    Ok(ret)
  }

  ///```
  /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
  /// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*};
  /// use std::{alloc::System, sync::Arc};
  ///
  /// hyperscan::alloc::chimera::set_chimera_allocator(Arc::new(System))?;
  ///
  /// let expr: ChimeraExpression = "(he)ll".parse()?;
  /// let db = expr.compile(ChimeraFlags::UTF8, ChimeraMode::NOGROUPS)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<&str> = Vec::new();
  /// let e = |_| ChimeraMatchResult::Continue;
  /// scratch.scan_sync(&db, "hello".into(), |m| {
  ///   matches.push(unsafe { m.source.as_str() });
  ///   ChimeraMatchResult::Continue
  /// }, e)?;
  /// assert_eq!(&matches, &["hell"]);
  /// # Ok(())
  /// # }
  /// ```
  pub fn set_chimera_allocator(
    allocator: Arc<impl GlobalAlloc+'static>,
  ) -> Result<(), ChimeraRuntimeError> {
    for f in [
      set_chimera_db_allocator,
      set_chimera_misc_allocator,
      set_chimera_scratch_allocator,
    ]
    .into_iter()
    {
      f(LayoutTracker::new(allocator.clone()))?;
    }
    Ok(())
  }
}
