/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{error::HyperscanRuntimeError, hs};

use libc;
use once_cell::sync::Lazy;
use parking_lot::Mutex;

use std::{
  alloc::{GlobalAlloc, Layout},
  collections::HashMap,
  mem, ops,
  os::raw::c_void,
  ptr::{self, NonNull},
  sync::Arc,
};

struct LayoutTracker {
  allocator: Arc<dyn GlobalAlloc>,
  layouts: HashMap<NonNull<u8>, Layout>,
}

/* NB: NonNull<u8> being non-Send disqualifies this as a default impl! */
unsafe impl Send for LayoutTracker {}

impl ops::Drop for LayoutTracker {
  fn drop(&mut self) {
    if !self.layouts.is_empty() {
      unreachable!("can't drop LayoutTracker with pending allocations!");
    }
  }
}

impl LayoutTracker {
  pub fn new(allocator: Arc<impl GlobalAlloc+'static>) -> Self {
    Self {
      allocator,
      layouts: HashMap::new(),
    }
  }

  pub fn allocate(&mut self, size: usize) -> Option<NonNull<u8>> {
    let layout = Layout::from_size_align(size, 8).unwrap();
    let ret = NonNull::new(unsafe { self.allocator.alloc(layout) });
    if let Some(ret) = ret {
      assert!(self.layouts.insert(ret, layout).is_none());
    }
    ret
  }

  pub fn deallocate(&mut self, ptr: NonNull<u8>) {
    let layout = self.layouts.remove(&ptr).unwrap();
    unsafe {
      self.allocator.dealloc(ptr.as_ptr(), layout);
    }
  }
}

static DB_ALLOCATOR: Lazy<Arc<Mutex<Option<LayoutTracker>>>> =
  Lazy::new(|| Arc::new(Mutex::new(None)));

unsafe extern "C" fn db_alloc_func(size: usize) -> *mut c_void {
  match DB_ALLOCATOR.lock().as_mut() {
    Some(allocator) => allocator
      .allocate(size)
      .map(|p| mem::transmute(p.as_ptr()))
      .unwrap_or(ptr::null_mut()),
    None => libc::malloc(size),
  }
}

unsafe extern "C" fn db_free_func(p: *mut c_void) {
  match DB_ALLOCATOR.lock().as_mut() {
    Some(allocator) => {
      if let Some(p) = NonNull::new(p as *mut u8) {
        allocator.deallocate(p);
      }
    },
    None => libc::free(p),
  }
}

pub fn set_db_allocator(
  allocator: Arc<impl GlobalAlloc+'static>,
) -> Result<(), HyperscanRuntimeError> {
  let tracker = LayoutTracker::new(allocator);
  let _ = DB_ALLOCATOR.lock().insert(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_database_allocator(Some(db_alloc_func), Some(db_free_func))
  })
}

static MISC_ALLOCATOR: Lazy<Arc<Mutex<Option<LayoutTracker>>>> =
  Lazy::new(|| Arc::new(Mutex::new(None)));


unsafe extern "C" fn misc_alloc_func(size: usize) -> *mut c_void {
  match MISC_ALLOCATOR.lock().as_mut() {
    Some(allocator) => allocator
      .allocate(size)
      .map(|p| mem::transmute(p.as_ptr()))
      .unwrap_or(ptr::null_mut()),
    None => libc::malloc(size),
  }
}

pub(crate) unsafe extern "C" fn misc_free_func(p: *mut c_void) {
  match MISC_ALLOCATOR.lock().as_mut() {
    Some(allocator) => {
      if let Some(p) = NonNull::new(p as *mut u8) {
        allocator.deallocate(p);
      }
    },
    None => libc::free(p),
  }
}

pub fn set_misc_allocator(
  allocator: Arc<impl GlobalAlloc+'static>,
) -> Result<(), HyperscanRuntimeError> {
  let tracker = LayoutTracker::new(allocator);
  let _ = MISC_ALLOCATOR.lock().insert(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_misc_allocator(Some(misc_alloc_func), Some(misc_free_func))
  })
}

static SCRATCH_ALLOCATOR: Lazy<Arc<Mutex<Option<LayoutTracker>>>> =
  Lazy::new(|| Arc::new(Mutex::new(None)));

unsafe extern "C" fn scratch_alloc_func(size: usize) -> *mut c_void {
  match SCRATCH_ALLOCATOR.lock().as_mut() {
    Some(allocator) => allocator
      .allocate(size)
      .map(|p| mem::transmute(p.as_ptr()))
      .unwrap_or(ptr::null_mut()),
    None => libc::malloc(size),
  }
}

unsafe extern "C" fn scratch_free_func(p: *mut c_void) {
  match SCRATCH_ALLOCATOR.lock().as_mut() {
    Some(allocator) => {
      if let Some(p) = NonNull::new(p as *mut u8) {
        allocator.deallocate(p);
      }
    },
    None => libc::free(p),
  }
}

pub fn set_scratch_allocator(
  allocator: Arc<impl GlobalAlloc+'static>,
) -> Result<(), HyperscanRuntimeError> {
  let tracker = LayoutTracker::new(allocator);
  let _ = SCRATCH_ALLOCATOR.lock().insert(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_scratch_allocator(Some(scratch_alloc_func), Some(scratch_free_func))
  })
}

static STREAM_ALLOCATOR: Lazy<Arc<Mutex<Option<LayoutTracker>>>> =
  Lazy::new(|| Arc::new(Mutex::new(None)));

unsafe extern "C" fn stream_alloc_func(size: usize) -> *mut c_void {
  match STREAM_ALLOCATOR.lock().as_mut() {
    Some(allocator) => allocator
      .allocate(size)
      .map(|p| mem::transmute(p.as_ptr()))
      .unwrap_or(ptr::null_mut()),
    None => libc::malloc(size),
  }
}

unsafe extern "C" fn stream_free_func(p: *mut c_void) {
  match STREAM_ALLOCATOR.lock().as_mut() {
    Some(allocator) => {
      if let Some(p) = NonNull::new(p as *mut u8) {
        allocator.deallocate(p);
      }
    },
    None => libc::free(p),
  }
}

pub fn set_stream_allocator(
  allocator: Arc<impl GlobalAlloc+'static>,
) -> Result<(), HyperscanRuntimeError> {
  let tracker = LayoutTracker::new(allocator);
  let _ = STREAM_ALLOCATOR.lock().insert(tracker);
  HyperscanRuntimeError::from_native(unsafe {
    hs::hs_set_stream_allocator(Some(stream_alloc_func), Some(stream_free_func))
  })
}

///```
/// # fn main() -> Result<(), hyperscan_async::error::HyperscanError> { tokio_test::block_on(async {
/// use hyperscan_async::{expression::*, flags::*, matchers::*};
/// use futures_util::TryStreamExt;
/// use std::{alloc::System, sync::Arc};
///
/// hyperscan_async::alloc::set_allocator(Arc::new(System))?;
///
/// let expr: Expression = "(he)ll".parse()?;
/// let db = expr.compile(Flags::UTF8, Mode::BLOCK)?;
///
/// let mut scratch = db.allocate_scratch()?;
///
/// let matches: Vec<&str> = scratch
///   .scan(&db, "hello".into(), ScanFlags::default(), |_| MatchResult::Continue)
///   .and_then(|m| async move { Ok(m.source.as_str()) })
///   .try_collect()
///   .await?;
/// assert_eq!(&matches, &["hell"]);
/// # Ok(())
/// # })}
/// ```
pub fn set_allocator(
  allocator: Arc<impl GlobalAlloc+'static>,
) -> Result<(), HyperscanRuntimeError> {
  set_db_allocator(allocator.clone())?;
  set_misc_allocator(allocator.clone())?;
  set_scratch_allocator(allocator.clone())?;
  set_stream_allocator(allocator)?;
  Ok(())
}

pub mod chimera {
  use super::*;
  use crate::error::chimera::*;

  /* FIXME: use RwLock instead? */
  static CHIMERA_DB_ALLOCATOR: Lazy<Arc<Mutex<Option<LayoutTracker>>>> =
    Lazy::new(|| Arc::new(Mutex::new(None)));

  unsafe extern "C" fn chimera_db_alloc_func(size: usize) -> *mut c_void {
    match CHIMERA_DB_ALLOCATOR.lock().as_mut() {
      Some(allocator) => allocator
        .allocate(size)
        .map(|p| mem::transmute(p.as_ptr()))
        .unwrap_or(ptr::null_mut()),
      None => libc::malloc(size),
    }
  }

  unsafe extern "C" fn chimera_db_free_func(p: *mut c_void) {
    match CHIMERA_DB_ALLOCATOR.lock().as_mut() {
      Some(allocator) => {
        if let Some(p) = NonNull::new(p as *mut u8) {
          allocator.deallocate(p);
        }
      },
      None => libc::free(p),
    }
  }

  pub fn set_chimera_db_allocator(
    allocator: Arc<impl GlobalAlloc+'static>,
  ) -> Result<(), ChimeraRuntimeError> {
    let tracker = LayoutTracker::new(allocator);
    let _ = CHIMERA_DB_ALLOCATOR.lock().insert(tracker);
    ChimeraRuntimeError::from_native(unsafe {
      hs::ch_set_database_allocator(Some(chimera_db_alloc_func), Some(chimera_db_free_func))
    })
  }

  static CHIMERA_MISC_ALLOCATOR: Lazy<Arc<Mutex<Option<LayoutTracker>>>> =
    Lazy::new(|| Arc::new(Mutex::new(None)));


  unsafe extern "C" fn chimera_misc_alloc_func(size: usize) -> *mut c_void {
    match CHIMERA_MISC_ALLOCATOR.lock().as_mut() {
      Some(allocator) => allocator
        .allocate(size)
        .map(|p| mem::transmute(p.as_ptr()))
        .unwrap_or(ptr::null_mut()),
      None => libc::malloc(size),
    }
  }

  pub(crate) unsafe extern "C" fn chimera_misc_free_func(p: *mut c_void) {
    match CHIMERA_MISC_ALLOCATOR.lock().as_mut() {
      Some(allocator) => {
        if let Some(p) = NonNull::new(p as *mut u8) {
          allocator.deallocate(p);
        }
      },
      None => libc::free(p),
    }
  }

  pub fn set_chimera_misc_allocator(
    allocator: Arc<impl GlobalAlloc+'static>,
  ) -> Result<(), ChimeraRuntimeError> {
    let tracker = LayoutTracker::new(allocator);
    let _ = CHIMERA_MISC_ALLOCATOR.lock().insert(tracker);
    ChimeraRuntimeError::from_native(unsafe {
      hs::ch_set_misc_allocator(Some(chimera_misc_alloc_func), Some(chimera_misc_free_func))
    })
  }

  static CHIMERA_SCRATCH_ALLOCATOR: Lazy<Arc<Mutex<Option<LayoutTracker>>>> =
    Lazy::new(|| Arc::new(Mutex::new(None)));

  unsafe extern "C" fn chimera_scratch_alloc_func(size: usize) -> *mut c_void {
    match CHIMERA_SCRATCH_ALLOCATOR.lock().as_mut() {
      Some(allocator) => allocator
        .allocate(size)
        .map(|p| mem::transmute(p.as_ptr()))
        .unwrap_or(ptr::null_mut()),
      None => libc::malloc(size),
    }
  }

  unsafe extern "C" fn chimera_scratch_free_func(p: *mut c_void) {
    match CHIMERA_SCRATCH_ALLOCATOR.lock().as_mut() {
      Some(allocator) => {
        if let Some(p) = NonNull::new(p as *mut u8) {
          allocator.deallocate(p);
        }
      },
      None => libc::free(p),
    }
  }

  pub fn set_chimera_scratch_allocator(
    allocator: Arc<impl GlobalAlloc+'static>,
  ) -> Result<(), ChimeraRuntimeError> {
    let tracker = LayoutTracker::new(allocator);
    let _ = CHIMERA_SCRATCH_ALLOCATOR.lock().insert(tracker);
    ChimeraRuntimeError::from_native(unsafe {
      hs::ch_set_scratch_allocator(
        Some(chimera_scratch_alloc_func),
        Some(chimera_scratch_free_func),
      )
    })
  }

  ///```
  /// # fn main() -> Result<(), hyperscan_async::error::chimera::ChimeraError> { tokio_test::block_on(async {
  /// use hyperscan_async::{expression::*, flags::*, matchers::chimera::*};
  /// use futures_util::TryStreamExt;
  /// use std::{alloc::System, sync::Arc};
  ///
  /// hyperscan_async::alloc::chimera::set_chimera_allocator(Arc::new(System))?;
  ///
  /// let expr: ChimeraExpression = "(he)ll".parse()?;
  /// let db = expr.compile(ChimeraFlags::UTF8, ChimeraMode::NOGROUPS)?;
  ///
  /// let mut scratch = db.allocate_scratch()?;
  ///
  /// let matches: Vec<&str> = scratch
  ///   .scan::<TrivialChimeraScanner>(&db, "hello".into(), ScanFlags::default())
  ///   .and_then(|m| async move { Ok(m.source.as_str()) })
  ///   .try_collect()
  ///   .await?;
  /// assert_eq!(&matches, &["hell"]);
  /// # Ok(())
  /// # })}
  /// ```
  pub fn set_chimera_allocator(
    allocator: Arc<impl GlobalAlloc+'static>,
  ) -> Result<(), ChimeraRuntimeError> {
    set_chimera_db_allocator(allocator.clone())?;
    set_chimera_misc_allocator(allocator.clone())?;
    set_chimera_scratch_allocator(allocator)?;
    Ok(())
  }
}
