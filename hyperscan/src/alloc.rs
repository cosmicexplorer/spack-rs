/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

//! Routines for overriding the allocators used in several components of
//! hyperscan.
//!
//! # Use Cases
//! [`set_allocator()`] will set all of the allocators at once, while the
//! `set_*_allocator()` methods such as [`set_db_allocator()`] enable overriding
//! allocation logic for individual components of hyperscan. In either case,
//! `get_*_allocator()` methods such as [`get_db_allocator()`] enable
//! introspection of the active allocator (which defaults to [`libc::malloc()`]
//! and [`libc::free()`] if unset).
//!
//! ## Nonstandard Allocators
//! These methods can be used to wrap nonstandard allocators such as
//! [jemalloc](https://docs.rs/jemallocator) for hyperscan usage:
//!
//!```
//! #[cfg(feature = "compiler")]
//! fn main() -> Result<(), hyperscan::error::HyperscanError> {
//!   use hyperscan::{expression::*, flags::*, matchers::*};
//!   use jemallocator::Jemalloc;
//!
//!   // Use jemalloc for all hyperscan allocations.
//!   hyperscan::alloc::set_allocator(Jemalloc.into())?;
//!
//!   // Everything works as normal.
//!   let expr: Expression = "(he)ll".parse()?;
//!   let db = expr.compile(Flags::UTF8, Mode::BLOCK)?;
//!
//!   let mut scratch = db.allocate_scratch()?;
//!
//!   let mut matches: Vec<&str> = Vec::new();
//!   scratch
//!     .scan_sync(&db, "hello".into(), |m| {
//!       matches.push(unsafe { m.source.as_str() });
//!       MatchResult::Continue
//!     })?;
//!   assert_eq!(&matches, &["hell"]);
//!   Ok(())
//! }
//! # #[cfg(not(feature = "compiler"))]
//! # fn main() {}
//! ```
//!
//! ## Inspecting Live Allocations
//! However, this module also supports inspecting live allocations with
//! [`LayoutTracker::current_allocations()`] without overriding the allocation
//! logic, by wrapping the standard [`System`](std::alloc::System) allocator:
//!
//!```
//! #[cfg(feature = "compiler")]
//! fn main() -> Result<(), hyperscan::error::HyperscanError> {
//!   use hyperscan::{expression::*, flags::*, database::*, alloc::*};
//!   use std::{alloc::System, mem::ManuallyDrop};
//!
//!   // Wrap the standard Rust System allocator.
//!   let tracker = LayoutTracker::new(System.into());
//!   // Register it as the allocator for databases.
//!   assert!(set_db_allocator(tracker)?.is_none());
//!
//!   // Create a database.
//!   let expr: Expression = "asdf".parse()?;
//!   let mut db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?;
//!
//!   // Get the database allocator we just registered and view its live allocations:
//!   let allocs = get_db_allocator().as_ref().unwrap().current_allocations();
//!   // Verify that only the single known db was allocated:
//!   assert_eq!(1, allocs.len());
//!   let (p, _layout) = allocs[0];
//!   let db_ptr: *mut NativeDb = db.as_mut_native();
//!   assert_eq!(p.as_ptr() as *mut NativeDb, db_ptr);
//!
//!   // Demonstrate that we can actually use this pointer as a reference to the database,
//!   // although we have to be careful not to run the drop code:
//!   let db = ManuallyDrop::new(unsafe { Database::from_native(p.as_ptr() as *mut NativeDb) });
//!   // We can inspect properties of the database with this reference:
//!   assert_eq!(db.database_size()?, 936);
//!   Ok(())
//! }
//! # #[cfg(not(feature = "compiler"))]
//! # fn main() {}
//! ```
//!
//! # Global State
//! These methods mutate global process state when setting function pointers for
//! alloc and free, so this module requires the `"alloc"` feature, which itself
//! requires the `"static"` feature which statically links the hyperscan native
//! library to ensure exclusive access to this global state.
//!
//! ## Lifetimes and Dangling Pointers
//! These methods enable resetting the registered allocator more than once over
//! the lifetime of the program, but trying to drop any object allocated with a
//! previous allocator will cause an error. The
//! [`ManuallyDrop`](mem::ManuallyDrop) and `from_native()` methods (such as
//! [`Database::from_native()`](crate::database::Database::from_native)) can be
//! used to manage the lifetime of objects across multiple allocators:
//!
//!```
//! #[cfg(feature = "compiler")]
//! fn main() -> Result<(), hyperscan::error::HyperscanError> {
//!   use hyperscan::{expression::*, flags::*, database::*, matchers::*, alloc::*};
//!   use std::{alloc::System, mem::ManuallyDrop};
//!
//!   // Set the process-global allocator to use for Database instances:
//!   let tracker = LayoutTracker::new(System.into());
//!   // There was no custom allocator registered yet.
//!   assert!(set_db_allocator(tracker)?.is_none());
//!
//!   let expr: Expression = "asdf".parse()?;
//!   // Use ManuallyDrop to avoid calling the hyperscan db free method,
//!   // since we will be invalidating the pointer by changing the allocator,
//!   // and the .try_drop() method and Drop impl both call into
//!   // whatever allocator is currently active to free the pointer, which will error.
//!   let mut db = ManuallyDrop::new(expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?);
//!
//!   // Change the allocator to a fresh LayoutTracker:
//!   let tracker = set_db_allocator(LayoutTracker::new(System.into()))?.unwrap();
//!   // Get the extant allocations from the old LayoutTracker:
//!   let allocs = tracker.current_allocations();
//!   // Verify that only the single known db was allocated:
//!   assert_eq!(1, allocs.len());
//!   let (p, layout) = allocs[0];
//!   let db_ptr: *mut NativeDb = db.as_mut_native();
//!   assert_eq!(p.as_ptr() as *mut NativeDb, db_ptr);
//!
//!   // Despite having reset the allocator, our previous db is still valid
//!   // and can be used for matching:
//!   let mut scratch = db.allocate_scratch()?;
//!   let mut matches: Vec<&str> = Vec::new();
//!   scratch.scan_sync(&db, "asdf asdf".into(), |m| {
//!     matches.push(unsafe { m.source.as_str() });
//!     MatchResult::Continue
//!   })?;
//!   assert_eq!(&matches, &["asdf", "asdf"]);
//!
//!   // We can deserialize something from somewhere else into the db handle:
//!   let expr: Literal = "hello".parse()?;
//!   let serialized_db = expr.compile(Flags::SOM_LEFTMOST, Mode::BLOCK)?.serialize()?;
//!   // Ensure the allocated database is large enough to contain the deserialized one:
//!   assert!(layout.size() >= serialized_db.deserialized_size()?);
//!   // NB: overwrite the old database!
//!   unsafe { serialized_db.deserialize_db_at(db.as_mut_native())?; }
//!
//!   // Reuse the same database object now:
//!   scratch.setup_for_db(&db)?;
//!   matches.clear();
//!   scratch.scan_sync(&db, "hello hello".into(), |m| {
//!     matches.push(unsafe { m.source.as_str() });
//!     MatchResult::Continue
//!   })?;
//!   assert_eq!(&matches, &["hello", "hello"]);
//!
//!   // Deallocate the db by hand here (ensure no other handles point to it):
//!   tracker.deallocate(p);
//!   // NB: `db` is now INVALID and points to FREED MEMORY!!!
//!   Ok(())
//! }
//! # #[cfg(not(feature = "compiler"))]
//! # fn main() {}
//! ```

use crate::{error::HyperscanRuntimeError, hs};

use indexmap::IndexMap;
use libc;
use parking_lot::RwLock;

use std::{
  alloc::{GlobalAlloc, Layout},
  mem, ops,
  os::raw::c_void,
  ptr::{self, NonNull},
  sync::Arc,
};

/// The alloc/free interface required by hyperscan methods.
///
/// This is named "malloc-like" because it mirrors the interface provided by
/// [`libc::malloc()`] and [`libc::free()`]. This differs from [`GlobalAlloc`]
/// in two ways:
/// - no [`Layout`] argument is provided to the deallocate method, so the
///   implementation must record the size of each allocation somewhere.
/// - only a `size` argument is provided to the allocate method, with the
///   *alignment* requirements of the memory being relegated to comments and
///   docstrings.
pub trait MallocLikeAllocator {
  /// Allocate a region of memory of at least `size` bytes.
  ///
  /// The alignment of the returned memory region is specified by the
  /// implementation. Returns [`None`] if allocation fails for any reason.
  fn allocate(&self, size: usize) -> Option<NonNull<u8>>;
  /// Free up a previously-allocated memory region at `ptr`.
  ///
  /// The value must be the exact same location returned by a previous call to
  /// [`Self::allocate()`]. The behavior if this method is called more than once
  /// for a given `ptr` is unspecified.
  fn deallocate(&self, ptr: NonNull<u8>);
}

/// An adapter for [`GlobalAlloc`] instances to implement
/// [`MallocLikeAllocator`].
///
/// This struct also supports introspecting the current allocation table with
/// [`Self::current_allocations()`]:
///```
/// use hyperscan::alloc::{LayoutTracker, MallocLikeAllocator};
/// use std::{slice, alloc::System};
///
/// let tracker = LayoutTracker::new(System.into());
/// let p1 = tracker.allocate(32).unwrap();
/// let p2 = tracker.allocate(64).unwrap();
///
/// let allocs = tracker.current_allocations();
/// assert_eq!(allocs.len(), 2);
/// let (p1_p, p1_layout) = allocs[0];
/// let (p2_p, p2_layout) = allocs[1];
/// assert_eq!(p1_p, p1);
/// assert!(p1_layout.size() >= 32);
/// assert!(p1_layout.align() >= 8);
/// assert_eq!(p2_p, p2);
/// assert!(p2_layout.size() >= 64);
/// assert!(p2_layout.align() >= 8);
///
/// // Note that modifying pointers in use by other threads may cause race conditions
/// // and undefined behavior!
/// let s1 = unsafe { slice::from_raw_parts_mut(p1_p.as_ptr(), p1_layout.size()) };
/// s1[..5].copy_from_slice(b"hello");
/// let s2 = unsafe { slice::from_raw_parts_mut(p2_p.as_ptr(), p2_layout.size()) };
/// s2[..5].copy_from_slice(&s1[..5]);
/// assert_eq!(&s2[..5], b"hello");
///
/// // Free memory when done:
/// tracker.deallocate(p1);
/// tracker.deallocate(p2);
/// ```
pub struct LayoutTracker {
  allocator: Arc<dyn GlobalAlloc>,
  layouts: RwLock<IndexMap<NonNull<u8>, Layout>>,
}

unsafe impl Send for LayoutTracker {}
unsafe impl Sync for LayoutTracker {}

impl LayoutTracker {
  /// Create a new allocation mapping which records the [`Layout`] argument for
  /// each allocation that goes to the underlying `allocator`.
  pub fn new(allocator: Arc<impl GlobalAlloc+'static>) -> Self {
    Self {
      allocator,
      layouts: RwLock::new(IndexMap::new()),
    }
  }

  /// Get a copy of the current live allocation mapping given a reference to
  /// this allocator.
  ///
  /// This struct makes use of an [`RwLock`] to allow concurrent access. Note
  /// that pointers may not be safe to dereference if they are freed after this
  /// method is called!
  pub fn current_allocations(&self) -> Vec<(NonNull<u8>, Layout)> {
    self.layouts.read().iter().map(|(x, y)| (*x, *y)).collect()
  }
}

/// [`LayoutTracker`] implements three additional guarantees over the base
/// [`MallocLikeAllocator`]:
/// - 0-size allocation requests always return [`None`] instead of allocating.
/// - all allocations are aligned to at least 8 bytes.
/// - attempted double frees will panic instead.
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
    assert!(self.layouts.write().insert(ret, layout).is_none());
    Some(ret)
  }

  fn deallocate(&self, ptr: NonNull<u8>) {
    let layout = self.layouts.write().remove(&ptr).unwrap();
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

/// Reset the allocator used for [`Database`](crate::database::Database)
/// instances.
pub fn set_db_allocator(
  tracker: LayoutTracker,
) -> Result<Option<LayoutTracker>, HyperscanRuntimeError> {
  let ret = DB_ALLOCATOR.write().replace(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_database_allocator(Some(db_alloc_func), Some(db_free_func))
  })?;
  Ok(ret)
}

/// Get the allocator used for [`Database`](crate::database::Database)
/// instances.
pub fn get_db_allocator() -> impl ops::Deref<Target=Option<LayoutTracker>> { DB_ALLOCATOR.read() }

allocator![MISC_ALLOCATOR, misc_alloc_func, misc_free_func];

/// Reset the allocator used for
/// [`MiscAllocation`](crate::database::MiscAllocation) instances.
pub fn set_misc_allocator(
  tracker: LayoutTracker,
) -> Result<Option<LayoutTracker>, HyperscanRuntimeError> {
  let ret = MISC_ALLOCATOR.write().replace(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_misc_allocator(Some(misc_alloc_func), Some(misc_free_func))
  })?;
  Ok(ret)
}

/// Get the allocator used for
/// [`MiscAllocation`](crate::database::MiscAllocation) instances.
pub fn get_misc_allocator() -> impl ops::Deref<Target=Option<LayoutTracker>> {
  MISC_ALLOCATOR.read()
}

allocator![SCRATCH_ALLOCATOR, scratch_alloc_func, scratch_free_func];

/// Reset the allocator used for [`Scratch`](crate::state::Scratch) instances.
pub fn set_scratch_allocator(
  tracker: LayoutTracker,
) -> Result<Option<LayoutTracker>, HyperscanRuntimeError> {
  let ret = SCRATCH_ALLOCATOR.write().replace(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_scratch_allocator(Some(scratch_alloc_func), Some(scratch_free_func))
  })?;
  Ok(ret)
}

/// Get the allocator used for [`Scratch`](crate::state::Scratch) instances.
pub fn get_scratch_allocator() -> impl ops::Deref<Target=Option<LayoutTracker>> {
  SCRATCH_ALLOCATOR.read()
}

allocator![STREAM_ALLOCATOR, stream_alloc_func, stream_free_func];

/// Reset the allocator used for [`LiveStream`](crate::stream::LiveStream)
/// instances.
pub fn set_stream_allocator(
  tracker: LayoutTracker,
) -> Result<Option<LayoutTracker>, HyperscanRuntimeError> {
  let ret = STREAM_ALLOCATOR.write().replace(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_stream_allocator(Some(stream_alloc_func), Some(stream_free_func))
  })?;
  Ok(ret)
}

/// Get the allocator used for [`LiveStream`](crate::stream::LiveStream)
/// instances.
pub fn get_stream_allocator() -> impl ops::Deref<Target=Option<LayoutTracker>> {
  STREAM_ALLOCATOR.read()
}

/// Convenience method to reset all hyperscan dynamic allocators at once.
///
/// Example: use [jemalloc](https://docs.rs/jemallocator) for all hyperscan allocations:
///
///```
/// #[cfg(feature = "compiler")]
/// fn main() -> Result<(), hyperscan::error::HyperscanError> {
///   use hyperscan::{expression::*, flags::*, matchers::*};
///   use jemallocator::Jemalloc;
///
///   // Use jemalloc for all hyperscan allocations.
///   hyperscan::alloc::set_allocator(Jemalloc.into())?;
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

/// Routines for overriding the allocators used in the chimera library.
///
/// # Use Cases
/// As with the base [`hyperscan#Use Cases`](crate::alloc#use-cases), this has setter methods
/// for all allocators at once, or for a single component at a time, as well as getter methods.
///
/// ## Nonstandard Allocators
/// It can wrap nonstandard allocators such as [jemalloc](https://docs.rs/jemallocator):
///
///```
/// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
/// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*};
/// use jemallocator::Jemalloc;
///
/// // Use jemalloc for all chimera allocations.
/// hyperscan::alloc::chimera::set_chimera_allocator(Jemalloc.into())?;
///
/// // Everything works as normal.
/// let expr: ChimeraExpression = "(he)ll".parse()?;
/// let db = expr.compile(ChimeraFlags::default(), ChimeraMode::GROUPS)?;
///
/// let mut scratch = db.allocate_scratch()?;
///
/// let mut matches: Vec<&str> = Vec::new();
/// let e = |_| ChimeraMatchResult::Continue;
/// scratch
///   .scan_sync(&db, "hello".into(), |m| {
///     matches.push(unsafe { m.captures[1].unwrap().as_str() });
///     ChimeraMatchResult::Continue
///   }, e)?;
/// assert_eq!(&matches, &["he"]);
/// # Ok(())
/// # }
/// ```
///
/// ## Inspecting Live Allocations
/// This module also supports inspecting live allocations with
/// [`LayoutTracker::current_allocations()`]:
///
///```
/// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
/// use hyperscan::{expression::chimera::*, flags::chimera::*, database::chimera::*, alloc::{*, chimera::*}};
/// use std::{alloc::System, mem::ManuallyDrop};
///
/// // Wrap the standard Rust System allocator.
/// let tracker = LayoutTracker::new(System.into());
/// // Register it as the allocator for databases.
/// assert!(set_chimera_db_allocator(tracker)?.is_none());
///
/// // Create a database.
/// let expr: ChimeraExpression = "asdf".parse()?;
/// let mut db = expr.compile(ChimeraFlags::default(), ChimeraMode::NOGROUPS)?;
///
/// // Get the database allocator we just registered and view its live allocations:
/// let allocs = get_chimera_db_allocator().as_ref().unwrap().current_allocations();
/// // Verify that only the single known db was allocated:
/// assert_eq!(1, allocs.len());
/// let (p, _layout) = allocs[0];
/// let db_ptr: *mut NativeChimeraDb = db.as_mut_native();
/// assert_eq!(p.as_ptr() as *mut NativeChimeraDb, db_ptr);
///
/// // Demonstrate that we can actually use this pointer as a reference to the database,
/// // although we have to be careful not to run the drop code:
/// let db = ManuallyDrop::new(unsafe { ChimeraDb::from_native(p.as_ptr() as *mut NativeChimeraDb) });
/// // We can inspect properties of the database with this reference:
/// assert_eq!(db.get_db_size()?, 1452);
/// # Ok(())
/// # }
/// ```
///
/// # Global State
/// Because the `"chimera"` feature already requires the `"static"` feature
/// (this is [enforced by the build
/// script](https://github.com/intel/hyperscan/blob/bc3b191ab56055e8560c7cdc161c289c4d76e3d2/CMakeLists.txt#L494)
/// in the hyperscan/chimera codebase), there are no additional restrictions
/// required to enable modification of process-global state (unlike the
/// corresponding [`hyperscan#Global State`](crate::alloc#global-state)).
///
/// ## Lifetimes and Dangling Pointers
/// Similar methods as in the parent
/// [`hyperscan#Lifetimes`](crate::alloc#lifetimes-and-dangling-pointers) can be
/// used to handle object lifetimes if multiple allocators are used over the
/// lifetime of the program.
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

  /// Reset the allocator used for
  /// [`ChimeraDb`](crate::database::chimera::ChimeraDb) instances.
  pub fn set_chimera_db_allocator(
    tracker: LayoutTracker,
  ) -> Result<Option<LayoutTracker>, ChimeraRuntimeError> {
    let ret = CHIMERA_DB_ALLOCATOR.write().replace(tracker);
    ChimeraRuntimeError::from_native(unsafe {
      hs::ch_set_database_allocator(Some(chimera_db_alloc_func), Some(chimera_db_free_func))
    })?;
    Ok(ret)
  }

  /// Get the allocator used for
  /// [`ChimeraDb`](crate::database::chimera::ChimeraDb) instances.
  pub fn get_chimera_db_allocator() -> impl ops::Deref<Target=Option<LayoutTracker>> {
    CHIMERA_DB_ALLOCATOR.read()
  }

  allocator![
    CHIMERA_MISC_ALLOCATOR,
    chimera_misc_alloc_func,
    chimera_misc_free_func
  ];

  /// Reset the allocator used for
  /// [`ChimeraMiscAllocation`](crate::database::chimera::ChimeraMiscAllocation)
  /// instances.
  pub fn set_chimera_misc_allocator(
    tracker: LayoutTracker,
  ) -> Result<Option<LayoutTracker>, ChimeraRuntimeError> {
    let ret = CHIMERA_MISC_ALLOCATOR.write().replace(tracker);
    ChimeraRuntimeError::from_native(unsafe {
      hs::ch_set_misc_allocator(Some(chimera_misc_alloc_func), Some(chimera_misc_free_func))
    })?;
    Ok(ret)
  }

  /// Get the allocator used for
  /// [`ChimeraMiscAllocation`](crate::database::chimera::ChimeraMiscAllocation)
  /// instances.
  pub fn get_chimera_misc_allocator() -> impl ops::Deref<Target=Option<LayoutTracker>> {
    CHIMERA_MISC_ALLOCATOR.read()
  }

  allocator![
    CHIMERA_SCRATCH_ALLOCATOR,
    chimera_scratch_alloc_func,
    chimera_scratch_free_func
  ];

  /// Reset the allocator used for
  /// [`ChimeraScratch`](crate::state::chimera::ChimeraScratch) instances.
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

  /// Get the allocator used for
  /// [`ChimeraScratch`](crate::state::chimera::ChimeraScratch) instances.
  pub fn get_chimera_scratch_allocator() -> impl ops::Deref<Target=Option<LayoutTracker>> {
    CHIMERA_SCRATCH_ALLOCATOR.read()
  }

  /// Convenience method to reset all chimera dynamic allocators at once.
  ///
  /// Example: use [jemalloc](https://docs.rs/jemallocator) for all chimera allocations:
  ///
  ///```
  /// # fn main() -> Result<(), hyperscan::error::chimera::ChimeraError> {
  /// use hyperscan::{expression::chimera::*, flags::chimera::*, matchers::chimera::*};
  /// use jemallocator::Jemalloc;
  ///
  /// // Use jemalloc for all chimera allocations.
  /// hyperscan::alloc::chimera::set_chimera_allocator(Jemalloc.into())?;
  ///
  /// let expr: ChimeraExpression = "(he)ll".parse()?;
  /// let db = expr.compile(ChimeraFlags::default(), ChimeraMode::GROUPS)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let mut matches: Vec<&str> = Vec::new();
  /// let e = |_| ChimeraMatchResult::Continue;
  /// scratch.scan_sync(&db, "hello".into(), |m| {
  ///   matches.push(unsafe { m.captures[1].unwrap().as_str() });
  ///   ChimeraMatchResult::Continue
  /// }, e)?;
  /// assert_eq!(&matches, &["he"]);
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
