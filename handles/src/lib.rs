/*
 * Description: Type-erased strategies for sharing and cloning resources.
 *
 * Copyright (C) 2023-2024 Danny McClanahan <dmcC2@hypnicjerk.ai>
 * SPDX-License-Identifier: Apache-2.0
 */

//! Type-erased strategies for sharing and cloning resources.

#![deny(rustdoc::missing_crate_level_docs)]
#![deny(missing_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
#![deny(clippy::all)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::result_large_err)]

use std::{any::Any, mem, ptr, rc::Rc, sync::Arc};

/// A mutable wrapper for a dynamic memory allocation which may fail.
///
/// The [`Any`] constraint enables downcasting any [`dyn`] object to a concrete
/// type with e.g. [`dyn Any::downcast_ref()`] or [`Box::downcast()`]. Note that
/// [`Any`] also requires the `'static` lifetime bound to do this and therefore
/// types implementing this trait may not hold any non-static reference fields.
/// This seemed like an appropriate tradeoff for something that is intended to
/// represent an allocation from some global memory pool.
///
/// [`dyn`]: https://doc.rust-lang.org/std/keyword.dyn.html
pub trait Resource: Any {
  /// Error type for allocation and deallocation.
  ///
  /// This can be [`()`](prim@unit) if the de/allocation are truly infallible.
  type Error;

  /// Request a new memory allocation, then initialize the allocation with the
  /// same state as `self`.
  fn deep_clone(&self) -> Result<Self, Self::Error>
  where Self: Sized;

  /// Similar to [`Self::deep_clone()`], but places the concrete type in a
  /// heap-allocated box.
  ///
  /// Because of the type erasure in the return value, this method is also
  /// accessible to `dyn Resource` vtable instances.
  fn deep_boxed_clone(&self) -> Result<Box<dyn Resource<Error=Self::Error>>, Self::Error>;

  /// Deallocate the memory and release any other resources that were owned by
  /// this specific object.
  ///
  /// This is intended for use with memory pooling smart pointer [`Handle`]s
  /// which may decide to execute the fallible deallocation method from any of
  /// the [`Handle`] methods that return [`Result`].
  ///
  /// # Safety
  /// Calling this method more than once is considered a double free, and
  /// attempting to use the object at all after calling this method is
  /// considered a use-after-free.
  unsafe fn sync_drop(&mut self) -> Result<(), Self::Error>;
}

/// A smart pointer strategy to switch between copy-on-write or copy-up-front
/// techniques.
///
/// As with [`Resource`], this trait requires [`Any`] in order to support
/// downcasting.
pub trait Handle: Any {
  /// The underlying fallible resource type that we want to hand out copies of.
  ///
  /// Note that [`Handle`] itself does not define its own error type. The "smart
  /// pointer" role of [`Handle`] is to perform *infallible* operations like
  /// reference counting, while letting [`Resource`] cover the clumsy fallible
  /// initialization work.
  type R: Resource;

  /// Given an unboxed resource, produce a handle that has exclusive access to
  /// the resource.
  fn wrap(r: Self::R) -> Self
  where Self: Sized;

  /// Given an unboxed handle, create another instance with a strong reference
  /// to it.
  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized;

  /// Similar to [`Self::clone_handle()`], but places the concrete type in a
  /// heap-allocated box.
  fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>, <Self::R as Resource>::Error>;

  /// Get a read-only reference to the underlying resource.
  fn handle_ref(&self) -> &Self::R;

  /// Return whether these two handles point to the same underlying resource
  /// allocation.
  fn eq_ref(&self, other: &dyn Handle<R=Self::R>) -> bool { equal_refs(self, other) }

  /// Return [`Some`] if this handle has exclusive access, else [`None`].
  fn get_mut(&mut self) -> Option<&mut Self::R>;

  /// If there are any other strong or weak references to the same resource,
  /// disassociate them and clone the resource if necessary.
  fn ensure_exclusive(&mut self) -> Result<(), <Self::R as Resource>::Error>;

  /// A combination of [`Self::ensure_exclusive()`] and [`Self::get_mut()`].
  fn make_mut(&mut self) -> Result<&mut Self::R, <Self::R as Resource>::Error> {
    self.ensure_exclusive()?;
    Ok(self.get_mut().unwrap())
  }
}

/// A free function implementation of [`Handle::eq_ref()`].
pub fn equal_refs<R: Resource+?Sized>(
  h1: &(impl Handle<R=R>+?Sized),
  h2: &(impl Handle<R=R>+?Sized),
) -> bool {
  ptr::eq(h1.handle_ref(), h2.handle_ref())
}

/// A handle can just be the thing itself, which means it's eagerly cloned.
impl<R: Resource> Handle for R {
  type R = Self;

  fn wrap(r: Self::R) -> Self
  where Self: Sized {
    r
  }

  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized {
    self.deep_clone()
  }

  fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>, <Self::R as Resource>::Error> {
    /* TODO: remove the transmute when https://github.com/rust-lang/rust/issues/65991 lands! */
    let r: Box<dyn Any> = unsafe { mem::transmute(self.deep_boxed_clone()?) };
    let h: Box<Self> = r.downcast().unwrap();
    Ok(h)
  }

  fn handle_ref(&self) -> &Self::R { self }

  fn get_mut(&mut self) -> Option<&mut Self::R> { Some(self) }

  fn ensure_exclusive(&mut self) -> Result<(), <Self::R as Resource>::Error> { Ok(()) }
}

/// An `Rc` will lazily clone, but can't be sent across threads.
impl<R: Resource> Handle for Rc<R> {
  type R = R;

  fn wrap(r: Self::R) -> Self
  where Self: Sized {
    Rc::new(r)
  }

  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized {
    Ok(Rc::clone(self))
  }

  fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>, <Self::R as Resource>::Error> {
    Ok(Box::new(Rc::clone(self)))
  }

  fn handle_ref(&self) -> &Self::R { self.as_ref() }

  fn get_mut(&mut self) -> Option<&mut Self::R> { Rc::get_mut(self) }

  fn ensure_exclusive(&mut self) -> Result<(), <Self::R as Resource>::Error> {
    if Rc::strong_count(self) != 1 {
      let new: R = self.as_ref().deep_clone()?;
      *self = Rc::new(new);
      return Ok(());
    }
    if Rc::weak_count(self) > 0 {
      unsafe {
        let mut tmp: mem::MaybeUninit<Rc<R>> = mem::MaybeUninit::uninit();
        let s: *mut Self = self;
        ptr::swap(s, tmp.as_mut_ptr());
        /* `self`/`s` is now invalid, and `tmp` is now valid! */
        /* strong_count == 1 was verified in the if, so this unwrap is safe: */
        let exclusive = Rc::into_inner(tmp.assume_init()).unwrap_unchecked();
        /* `tmp` is consumed! */
        s.write(Rc::new(exclusive));
        /* `self` is now valid again! */
      }
    }
    Ok(())
  }
}

/// An `Arc` will lazily clone and *can* be sent across threads.
impl<R: Resource> Handle for Arc<R> {
  type R = R;

  fn wrap(r: Self::R) -> Self
  where Self: Sized {
    Arc::new(r)
  }

  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized {
    Ok(Arc::clone(self))
  }

  fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>, <Self::R as Resource>::Error> {
    Ok(Box::new(Arc::clone(self)))
  }

  fn handle_ref(&self) -> &Self::R { self.as_ref() }

  fn get_mut(&mut self) -> Option<&mut Self::R> { Arc::get_mut(self) }

  fn ensure_exclusive(&mut self) -> Result<(), <Self::R as Resource>::Error> {
    if Arc::strong_count(self) != 1 {
      let new: R = self.as_ref().deep_clone()?;
      *self = Arc::new(new);
      return Ok(());
    }
    if Arc::weak_count(self) > 0 {
      unsafe {
        let mut tmp: mem::MaybeUninit<Arc<R>> = mem::MaybeUninit::uninit();
        let s: *mut Self = self;
        ptr::swap(s, tmp.as_mut_ptr());
        /* `self`/`s` is now invalid, and `tmp` is now valid! */
        /* strong_count == 1 was verified in the if, so this unwrap is safe: */
        let exclusive = Arc::into_inner(tmp.assume_init()).unwrap_unchecked();
        /* `tmp` is consumed! */
        s.write(Arc::new(exclusive));
        /* `self` is now valid again! */
      }
    }
    Ok(())
  }
}

#[cfg(test)]
mod test {
  use super::*;

  #[derive(Debug, PartialEq, Eq)]
  struct R {
    pub state: u8,
  }

  impl Resource for R {
    type Error = ();
    fn deep_clone(&self) -> Result<Self, ()> { Ok(Self { state: self.state }) }
    fn deep_boxed_clone(&self) -> Result<Box<dyn Resource<Error=()>>, Self::Error> {
      Ok(Box::new(Self { state: self.state }))
    }
    unsafe fn sync_drop(&mut self) -> Result<(), ()> { Ok(()) }
  }

  #[test]
  fn test_bare() {
    let r = R { state: 0 };
    let mut r1 = r.clone_handle().unwrap();

    /* Because we do not use any wrapper or smart pointer, cloning a "bare
     * handle" immediately invokes a new allocation. */
    assert_eq!(r, r1);
    assert!(!r.eq_ref(&r1));

    r1.ensure_exclusive().unwrap();
    assert_eq!(r, r1);
    assert!(!r.eq_ref(&r1));

    r1.make_mut().unwrap().state = 1;
    assert_ne!(r, r1);
    assert!(!r.eq_ref(&r1));
  }

  #[test]
  fn test_rc() {
    let r = Rc::new(R { state: 0 });
    let mut r1 = r.clone_handle().unwrap();

    /* Copy-on-write semantics with lazy cloning. */
    assert_eq!(r, r1);
    assert!(r.eq_ref(&r1));

    r1.ensure_exclusive().unwrap();
    assert_eq!(r, r1);
    assert!(!r.eq_ref(&r1));

    r1.make_mut().unwrap().state = 1;
    assert_ne!(r, r1);
    assert!(!r.eq_ref(&r1));
  }

  #[test]
  fn test_arc() {
    let r = Arc::new(R { state: 0 });
    let mut r1 = r.clone_handle().unwrap();

    /* Copy-on-write semantics with lazy cloning. */
    assert_eq!(r, r1);
    assert!(r.eq_ref(&r1));

    r1.ensure_exclusive().unwrap();
    assert_eq!(r, r1);
    assert!(!r.eq_ref(&r1));

    r1.make_mut().unwrap().state = 1;
    assert_ne!(r, r1);
    assert!(!r.eq_ref(&r1));
  }

  #[test]
  fn test_interchange() {
    let mut r = Box::new(R { state: 0 });
    let r1: &mut dyn Handle<R=R> = r.as_mut();
    let r2 = r1.boxed_clone_handle().unwrap();

    let r2_test1: Box<dyn Any> = r2.boxed_clone_handle().unwrap();
    let r2_test2: Box<dyn Any> = r2.boxed_clone_handle().unwrap();
    assert!(r2_test1.downcast::<Rc<R>>().is_err());
    assert!(r2_test2.downcast::<Arc<R>>().is_err());
    let r2: Box<dyn Any> = r2;
    let mut r2: Box<R> = r2.downcast().unwrap();

    assert_eq!(r1.handle_ref(), r2.handle_ref());
    assert!(!r1.eq_ref(r2.as_ref()));
    /* Should do nothing, since both are unwrapped ("bare") handles. */
    r1.ensure_exclusive().unwrap();
    r2.ensure_exclusive().unwrap();

    let mut r3 = Rc::new(R { state: 0 });
    let r3: &mut dyn Handle<R=R> = &mut r3;
    let r4 = r3.boxed_clone_handle().unwrap();

    let r4_test1: Box<dyn Any> = r4.boxed_clone_handle().unwrap();
    let r4_test2: Box<dyn Any> = r4.boxed_clone_handle().unwrap();
    assert!(r4_test1.downcast::<R>().is_err());
    assert!(r4_test2.downcast::<Arc<R>>().is_err());
    let r4: Box<dyn Any> = r4;
    let r4: Box<Rc<R>> = r4.downcast().unwrap();

    assert_eq!(r3.handle_ref(), r4.handle_ref());
    assert_eq!(r3.handle_ref(), r1.handle_ref());
    assert!(r3.eq_ref(r4.as_ref()));
    /* Demonstrate that eq_ref() still works for different types of handles. */
    assert!(!r3.eq_ref(r1));

    r3.ensure_exclusive().unwrap();
    assert_eq!(r3.handle_ref(), r4.handle_ref());
    assert!(!r3.eq_ref(r4.as_ref()));
    r3.get_mut().unwrap().state = 1;
    assert_ne!(r3.handle_ref(), r4.handle_ref());

    let mut r5 = Arc::new(R { state: 0 });
    let r5: &mut dyn Handle<R=R> = &mut r5;
    let r6 = r5.boxed_clone_handle().unwrap();

    let r6_test1: Box<dyn Any> = r6.boxed_clone_handle().unwrap();
    let r6_test2: Box<dyn Any> = r6.boxed_clone_handle().unwrap();
    assert!(r6_test1.downcast::<R>().is_err());
    assert!(r6_test2.downcast::<Rc<R>>().is_err());
    let r6: Box<dyn Any> = r6;
    let r6: Box<Arc<R>> = r6.downcast().unwrap();

    assert_eq!(r5.handle_ref(), r6.handle_ref());
    assert_eq!(r5.handle_ref(), r1.handle_ref());
    assert!(r5.eq_ref(r6.as_ref()));
    /* Demonstrate that eq_ref() still compiles for different types of handles. */
    assert!(!r5.eq_ref(r1));
    assert!(!r5.eq_ref(r3));

    r5.ensure_exclusive().unwrap();
    assert_eq!(r5.handle_ref(), r6.handle_ref());
    assert!(!r5.eq_ref(r6.as_ref()));
    r5.get_mut().unwrap().state = 1;
    assert_ne!(r5.handle_ref(), r6.handle_ref());
  }
}
