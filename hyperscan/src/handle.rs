/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

use std::{mem::MaybeUninit, ptr, rc::Rc, sync::Arc};

pub trait Resource {
  type Error;

  fn deep_clone(&self) -> Result<Self, Self::Error>
  where Self: Sized;

  fn deep_boxed_clone(&self) -> Result<Box<dyn Resource<Error=Self::Error>>, Self::Error>;

  unsafe fn sync_drop(&mut self) -> Result<(), Self::Error>;
}

pub trait Handle {
  type R: Resource;

  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized;

  fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>, <Self::R as Resource>::Error>;

  fn handle_ref(&self) -> &Self::R;

  fn make_mut(&mut self) -> Result<&mut Self::R, <Self::R as Resource>::Error>;
}

pub fn equal_refs<H: Handle>(h1: &H, h2: &H) -> bool {
  let p1: *const H::R = h1.handle_ref();
  let p2: *const H::R = h2.handle_ref();
  p1 == p2
}

impl<R: Resource> Handle for R {
  type R = Self;

  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized {
    self.deep_clone()
  }

  fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>, <Self::R as Resource>::Error> {
    todo!()
    /* self.deep_boxed_clone() */
  }

  fn handle_ref(&self) -> &Self::R { self }

  fn make_mut(&mut self) -> Result<&mut Self::R, <Self::R as Resource>::Error> { Ok(self) }
}

/* impl<E> Handle for Box<dyn Resource<Error=E>> { */
/* type R = Box<dyn Resource<Error=E>>; */

/* fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error> */
/* where Self: Sized { */
/* self.deep_clone() */
/* } */

/* fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>,
 * <Self::R as Resource>::Error> { */
/* self.deep_boxed_clone() */
/* } */

/* fn handle_ref(&self) -> &Self::R { self } */

/* fn make_mut(&mut self) -> Result<&mut Self::R, <Self::R as
 * Resource>::Error> { Ok(self) } */
/* } */

impl<R: Resource+'static> Handle for Rc<R> {
  type R = R;

  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized {
    Ok(Rc::clone(self))
  }

  fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>, <Self::R as Resource>::Error> {
    Ok(Box::new(Rc::clone(self)))
  }

  fn handle_ref(&self) -> &Self::R { self.as_ref() }

  fn make_mut(&mut self) -> Result<&mut Self::R, <Self::R as Resource>::Error> {
    if Rc::strong_count(self) != 1 {
      let new: R = self.as_ref().deep_clone()?;
      *self = Rc::new(new);
    } else if Rc::weak_count(self) > 0 {
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
    /* get_mut() only works if strong_count is 1 and weak_count is 0, which is
     * what we should have just ensured above. */
    Ok(Rc::get_mut(self).unwrap())
  }
}

impl<R: Resource+'static> Handle for Arc<R> {
  type R = R;

  fn clone_handle(&self) -> Result<Self, <Self::R as Resource>::Error>
  where Self: Sized {
    Ok(Arc::clone(self))
  }

  fn boxed_clone_handle(&self) -> Result<Box<dyn Handle<R=Self::R>>, <Self::R as Resource>::Error> {
    Ok(Box::new(Arc::clone(self)))
  }

  fn handle_ref(&self) -> &Self::R { self.as_ref() }

  fn make_mut(&mut self) -> Result<&mut Self::R, <Self::R as Resource>::Error> {
    if Arc::strong_count(self) != 1 {
      let new: R = self.as_ref().deep_clone()?;
      *self = Arc::new(new);
    } else if Arc::weak_count(self) > 0 {
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
    /* get_mut() only works if strong_count is 1 and weak_count is 0, which is
     * what we should have just ensured above. */
    Ok(Arc::get_mut(self).unwrap())
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
    assert!(!equal_refs(&r, &r1));

    let _ = r1.make_mut().unwrap();
    assert_eq!(r, r1);
    assert!(!equal_refs(&r, &r1));

    r1.make_mut().unwrap().state = 1;
    assert_ne!(r, r1);
    assert!(!equal_refs(&r, &r1));
  }

  #[test]
  fn test_rc() {
    let r = Rc::new(R { state: 0 });
    let mut r1 = r.clone_handle().unwrap();

    /* Copy-on-write semantics with lazy cloning. */
    assert_eq!(r, r1);
    assert!(equal_refs(&r, &r1));

    let _ = r1.make_mut().unwrap();
    assert_eq!(r, r1);
    assert!(!equal_refs(&r, &r1));

    r1.make_mut().unwrap().state = 1;
    assert_ne!(r, r1);
    assert!(!equal_refs(&r, &r1));
  }

  #[test]
  fn test_arc() {
    let r = Arc::new(R { state: 0 });
    let mut r1 = r.clone_handle().unwrap();

    /* Copy-on-write semantics with lazy cloning. */
    assert_eq!(r, r1);
    assert!(equal_refs(&r, &r1));

    let _ = r1.make_mut().unwrap();
    assert_eq!(r, r1);
    assert!(!equal_refs(&r, &r1));

    r1.make_mut().unwrap().state = 1;
    assert_ne!(r, r1);
    assert!(!equal_refs(&r, &r1));
  }
}
