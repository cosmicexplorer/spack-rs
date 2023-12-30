/*
 * Description: Type-erased strategies for sharing and cloning resources.
 *
 * Copyright (C) 2023 Danny McClanahan <dmcC2@hypnicjerk.ai>
 * SPDX-License-Identifier: Apache-2.0
 */

#![warn(rustdoc::missing_crate_level_docs)]
#![allow(missing_docs)]
/* Make all doctests fail if they produce any warnings. */
#![doc(test(attr(deny(warnings))))]
#![deny(clippy::all)]
#![allow(clippy::collapsible_else_if)]
#![allow(clippy::result_large_err)]

use std::{any::Any, mem::MaybeUninit, ptr, rc::Rc, sync::Arc};

pub trait Resource: Any {
  type Error;

  fn deep_clone(&self) -> Result<Self, Self::Error>
  where Self: Sized;

  fn deep_boxed_clone(&self) -> Result<Box<dyn Resource<Error=Self::Error>>, Self::Error>;

  unsafe fn sync_drop(&mut self) -> Result<(), Self::Error>;
}

pub trait Handle: Any {
  type R: Resource;

  fn wrap(r: Self::R) -> Self
  where Self: Sized;

  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized;

  fn boxed_clone_handle<'a>(
    &self,
  ) -> Result<Box<dyn Handle<R=Self::R>+'a>, <Self::R as Resource>::Error>
  where Self: 'a;

  fn handle_ref(&self) -> &Self::R;

  fn eq_ref(&self, other: &dyn Handle<R=Self::R>) -> bool { equal_refs(self, other) }

  fn get_mut(&mut self) -> Option<&mut Self::R>;

  fn ensure_exclusive(&mut self) -> Result<(), <Self::R as Resource>::Error>;

  fn make_mut(&mut self) -> Result<&mut Self::R, <Self::R as Resource>::Error> {
    self.ensure_exclusive()?;
    Ok(self.get_mut().unwrap())
  }
}

pub fn equal_refs<R: Resource+?Sized>(
  h1: &(impl Handle<R=R>+?Sized),
  h2: &(impl Handle<R=R>+?Sized),
) -> bool {
  ptr::eq(h1.handle_ref(), h2.handle_ref())
}

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

  fn boxed_clone_handle<'a>(
    &self,
  ) -> Result<Box<dyn Handle<R=Self::R>+'a>, <Self::R as Resource>::Error>
  where Self: 'a {
    let r: Box<dyn Any> = self.deep_boxed_clone()?;
    let h: Box<Self> = r.downcast().unwrap();
    Ok(h)
  }

  fn handle_ref(&self) -> &Self::R { self }

  fn get_mut(&mut self) -> Option<&mut Self::R> { Some(self) }

  fn ensure_exclusive(&mut self) -> Result<(), <Self::R as Resource>::Error> { Ok(()) }
}

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

  fn boxed_clone_handle<'a>(
    &self,
  ) -> Result<Box<dyn Handle<R=Self::R>+'a>, <Self::R as Resource>::Error>
  where Self: 'a {
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
        let mut tmp: MaybeUninit<Rc<R>> = MaybeUninit::uninit();
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

  fn boxed_clone_handle<'a>(
    &self,
  ) -> Result<Box<dyn Handle<R=Self::R>+'a>, <Self::R as Resource>::Error>
  where Self: 'a {
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
        let mut tmp: MaybeUninit<Arc<R>> = MaybeUninit::uninit();
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
    let r1: &mut dyn AnyHandle<R=R> = r.as_mut();
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
    let r3: &mut dyn AnyHandle<R=R> = &mut r3;
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
    let r5: &mut dyn AnyHandle<R=R> = &mut r5;
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
