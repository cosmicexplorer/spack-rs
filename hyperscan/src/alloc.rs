/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use crate::{error::HyperscanError, hs};

use libc;
use once_cell::sync::Lazy;
use parking_lot::Mutex;

use std::{
  alloc::{Allocator, Layout},
  collections::HashMap,
  mem, ops,
  os::raw::c_void,
  ptr::{self, NonNull},
  sync::Arc,
};

struct LayoutTracker {
  allocator: Arc<dyn Allocator>,
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
  pub fn new(allocator: Arc<impl Allocator+'static>) -> Self {
    Self {
      allocator,
      layouts: HashMap::new(),
    }
  }

  pub fn allocate(&mut self, size: usize) -> Option<NonNull<u8>> {
    let layout = Layout::from_size_align(size, 8).unwrap();
    if let Some(ret_slice) = self.allocator.allocate(layout).ok() {
      let ret: NonNull<u8> = NonNull::new(ret_slice.as_mut_ptr()).unwrap();
      assert!(self.layouts.insert(ret, layout).is_none());
      Some(ret)
    } else {
      None
    }
  }

  pub fn deallocate(&mut self, ptr: NonNull<u8>) {
    let layout = self.layouts.remove(&ptr).unwrap();
    unsafe {
      self.allocator.deallocate(ptr, layout);
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

pub fn set_db_allocator(allocator: Arc<impl Allocator+'static>) -> Result<(), HyperscanError> {
  let tracker = LayoutTracker::new(allocator);
  let _ = DB_ALLOCATOR.lock().insert(tracker);
  HyperscanError::from_native(unsafe {
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

pub fn set_misc_allocator(allocator: Arc<impl Allocator+'static>) -> Result<(), HyperscanError> {
  let tracker = LayoutTracker::new(allocator);
  let _ = MISC_ALLOCATOR.lock().insert(tracker);
  HyperscanError::from_native(unsafe {
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

pub fn set_scratch_allocator(allocator: Arc<impl Allocator+'static>) -> Result<(), HyperscanError> {
  let tracker = LayoutTracker::new(allocator);
  let _ = SCRATCH_ALLOCATOR.lock().insert(tracker);
  HyperscanError::from_native(unsafe {
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

pub fn set_stream_allocator(allocator: Arc<impl Allocator+'static>) -> Result<(), HyperscanError> {
  let tracker = LayoutTracker::new(allocator);
  let _ = STREAM_ALLOCATOR.lock().insert(tracker);
  HyperscanError::from_native(unsafe {
    hs::hs_set_stream_allocator(Some(stream_alloc_func), Some(stream_free_func))
  })
}

///```
/// # #![feature(allocator_api)]
/// # fn main() -> Result<(), hyperscan::error::HyperscanCompileError> { tokio_test::block_on(async {
/// use hyperscan::{expression::*, flags::*, matchers::*};
/// use futures_util::TryStreamExt;
/// use std::{alloc::Global, pin::Pin, sync::Arc};
///
/// hyperscan::alloc::set_allocator(Arc::new(Global))?;
///
/// let expr: Expression = "(he)ll".parse()?;
/// let db = expr.compile(Flags::UTF8, Mode::BLOCK)?;
///
/// let mut scratch = db.allocate_scratch()?;
///
/// let matches: Vec<&str> = Pin::new(&mut scratch)
///   .scan(Pin::new(&db), "hello".into(), ScanFlags::default(), |_| MatchResult::Continue)
///   .and_then(|m| async move { Ok(m.source.as_str()) })
///   .try_collect()
///   .await?;
/// assert_eq!(&matches, &["hell"]);
/// # Ok(())
/// # })}
/// ```
pub fn set_allocator(allocator: Arc<impl Allocator+'static>) -> Result<(), HyperscanError> {
  set_db_allocator(allocator.clone())?;
  set_misc_allocator(allocator.clone())?;
  set_scratch_allocator(allocator.clone())?;
  set_stream_allocator(allocator)?;
  Ok(())
}
