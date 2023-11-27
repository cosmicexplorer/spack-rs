/* automatically generated by rust-bindgen 0.69.1 */

#[allow(non_snake_case, non_camel_case_types, non_upper_case_globals)]
pub mod root {
  #[allow(unused_imports)]
  use self::super::root;
  pub const HS_MAJOR: u8 = 5;
  pub const HS_MINOR: u8 = 4;
  pub const HS_PATCH: u8 = 2;
  pub const HS_SUCCESS: u8 = 0;
  pub const HS_INVALID: i8 = -1;
  pub const HS_NOMEM: i8 = -2;
  pub const HS_SCAN_TERMINATED: i8 = -3;
  pub const HS_COMPILER_ERROR: i8 = -4;
  pub const HS_DB_VERSION_ERROR: i8 = -5;
  pub const HS_DB_PLATFORM_ERROR: i8 = -6;
  pub const HS_DB_MODE_ERROR: i8 = -7;
  pub const HS_BAD_ALIGN: i8 = -8;
  pub const HS_BAD_ALLOC: i8 = -9;
  pub const HS_SCRATCH_IN_USE: i8 = -10;
  pub const HS_ARCH_ERROR: i8 = -11;
  pub const HS_INSUFFICIENT_SPACE: i8 = -12;
  pub const HS_UNKNOWN_ERROR: i8 = -13;
  pub const HS_EXT_FLAG_MIN_OFFSET: u8 = 1;
  pub const HS_EXT_FLAG_MAX_OFFSET: u8 = 2;
  pub const HS_EXT_FLAG_MIN_LENGTH: u8 = 4;
  pub const HS_EXT_FLAG_EDIT_DISTANCE: u8 = 8;
  pub const HS_EXT_FLAG_HAMMING_DISTANCE: u8 = 16;
  pub const HS_FLAG_CASELESS: u8 = 1;
  pub const HS_FLAG_DOTALL: u8 = 2;
  pub const HS_FLAG_MULTILINE: u8 = 4;
  pub const HS_FLAG_SINGLEMATCH: u8 = 8;
  pub const HS_FLAG_ALLOWEMPTY: u8 = 16;
  pub const HS_FLAG_UTF8: u8 = 32;
  pub const HS_FLAG_UCP: u8 = 64;
  pub const HS_FLAG_PREFILTER: u8 = 128;
  pub const HS_FLAG_SOM_LEFTMOST: u16 = 256;
  pub const HS_FLAG_COMBINATION: u16 = 512;
  pub const HS_FLAG_QUIET: u16 = 1024;
  pub const HS_CPU_FEATURES_AVX2: u8 = 4;
  pub const HS_CPU_FEATURES_AVX512: u8 = 8;
  pub const HS_CPU_FEATURES_AVX512VBMI: u8 = 16;
  pub const HS_TUNE_FAMILY_GENERIC: u8 = 0;
  pub const HS_TUNE_FAMILY_SNB: u8 = 1;
  pub const HS_TUNE_FAMILY_IVB: u8 = 2;
  pub const HS_TUNE_FAMILY_HSW: u8 = 3;
  pub const HS_TUNE_FAMILY_SLM: u8 = 4;
  pub const HS_TUNE_FAMILY_BDW: u8 = 5;
  pub const HS_TUNE_FAMILY_SKL: u8 = 6;
  pub const HS_TUNE_FAMILY_SKX: u8 = 7;
  pub const HS_TUNE_FAMILY_GLM: u8 = 8;
  pub const HS_TUNE_FAMILY_ICL: u8 = 9;
  pub const HS_TUNE_FAMILY_ICX: u8 = 10;
  pub const HS_MODE_BLOCK: u8 = 1;
  pub const HS_MODE_NOSTREAM: u8 = 1;
  pub const HS_MODE_STREAM: u8 = 2;
  pub const HS_MODE_VECTORED: u8 = 4;
  pub const HS_MODE_SOM_HORIZON_LARGE: u32 = 16777216;
  pub const HS_MODE_SOM_HORIZON_MEDIUM: u32 = 33554432;
  pub const HS_MODE_SOM_HORIZON_SMALL: u32 = 67108864;
  pub const HS_OFFSET_PAST_HORIZON: i8 = -1;
  pub mod std {
    #[allow(unused_imports)]
    use self::super::super::root;
  }
  pub mod __gnu_cxx {
    #[allow(unused_imports)]
    use self::super::super::root;
  }
  #[repr(C)]
  #[derive(Debug, Copy, Clone)]
  pub struct hs_database {
    _unused: [u8; 0],
  }
  pub type hs_database_t = root::hs_database;
  pub type hs_error_t = ::std::os::raw::c_int;
  extern "C" {
    pub fn hs_free_database(db: *mut root::hs_database_t) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_serialize_database(
      db: *const root::hs_database_t,
      bytes: *mut *mut ::std::os::raw::c_char,
      length: *mut usize,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_deserialize_database(
      bytes: *const ::std::os::raw::c_char,
      length: usize,
      db: *mut *mut root::hs_database_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_deserialize_database_at(
      bytes: *const ::std::os::raw::c_char,
      length: usize,
      db: *mut root::hs_database_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_stream_size(
      database: *const root::hs_database_t,
      stream_size: *mut usize,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_database_size(
      database: *const root::hs_database_t,
      database_size: *mut usize,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_serialized_database_size(
      bytes: *const ::std::os::raw::c_char,
      length: usize,
      deserialized_size: *mut usize,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_database_info(
      database: *const root::hs_database_t,
      info: *mut *mut ::std::os::raw::c_char,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_serialized_database_info(
      bytes: *const ::std::os::raw::c_char,
      length: usize,
      info: *mut *mut ::std::os::raw::c_char,
    ) -> root::hs_error_t;
  }
  pub type hs_alloc_t =
    ::std::option::Option<unsafe extern "C" fn(size: usize) -> *mut ::std::os::raw::c_void>;
  pub type hs_free_t =
    ::std::option::Option<unsafe extern "C" fn(ptr: *mut ::std::os::raw::c_void)>;
  extern "C" {
    pub fn hs_set_allocator(
      alloc_func: root::hs_alloc_t,
      free_func: root::hs_free_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_set_database_allocator(
      alloc_func: root::hs_alloc_t,
      free_func: root::hs_free_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_set_misc_allocator(
      alloc_func: root::hs_alloc_t,
      free_func: root::hs_free_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_set_scratch_allocator(
      alloc_func: root::hs_alloc_t,
      free_func: root::hs_free_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_set_stream_allocator(
      alloc_func: root::hs_alloc_t,
      free_func: root::hs_free_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_version() -> *const ::std::os::raw::c_char;
  }
  extern "C" {
    pub fn hs_valid_platform() -> root::hs_error_t;
  }
  #[repr(C)]
  #[derive(Debug, Copy, Clone)]
  pub struct hs_compile_error {
    pub message: *mut ::std::os::raw::c_char,
    pub expression: ::std::os::raw::c_int,
  }
  #[test]
  fn bindgen_test_layout_hs_compile_error() {
    const UNINIT: ::std::mem::MaybeUninit<hs_compile_error> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
      ::std::mem::size_of::<hs_compile_error>(),
      16usize,
      concat!("Size of: ", stringify!(hs_compile_error))
    );
    assert_eq!(
      ::std::mem::align_of::<hs_compile_error>(),
      8usize,
      concat!("Alignment of ", stringify!(hs_compile_error))
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).message) as usize - ptr as usize },
      0usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_compile_error),
        "::",
        stringify!(message)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).expression) as usize - ptr as usize },
      8usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_compile_error),
        "::",
        stringify!(expression)
      )
    );
  }
  pub type hs_compile_error_t = root::hs_compile_error;
  #[repr(C)]
  #[derive(Debug, Copy, Clone)]
  pub struct hs_platform_info {
    pub tune: ::std::os::raw::c_uint,
    pub cpu_features: ::std::os::raw::c_ulonglong,
    pub reserved1: ::std::os::raw::c_ulonglong,
    pub reserved2: ::std::os::raw::c_ulonglong,
  }
  #[test]
  fn bindgen_test_layout_hs_platform_info() {
    const UNINIT: ::std::mem::MaybeUninit<hs_platform_info> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
      ::std::mem::size_of::<hs_platform_info>(),
      32usize,
      concat!("Size of: ", stringify!(hs_platform_info))
    );
    assert_eq!(
      ::std::mem::align_of::<hs_platform_info>(),
      8usize,
      concat!("Alignment of ", stringify!(hs_platform_info))
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).tune) as usize - ptr as usize },
      0usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_platform_info),
        "::",
        stringify!(tune)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).cpu_features) as usize - ptr as usize },
      8usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_platform_info),
        "::",
        stringify!(cpu_features)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).reserved1) as usize - ptr as usize },
      16usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_platform_info),
        "::",
        stringify!(reserved1)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).reserved2) as usize - ptr as usize },
      24usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_platform_info),
        "::",
        stringify!(reserved2)
      )
    );
  }
  pub type hs_platform_info_t = root::hs_platform_info;
  #[repr(C)]
  #[derive(Debug, Copy, Clone)]
  pub struct hs_expr_info {
    pub min_width: ::std::os::raw::c_uint,
    pub max_width: ::std::os::raw::c_uint,
    pub unordered_matches: ::std::os::raw::c_char,
    pub matches_at_eod: ::std::os::raw::c_char,
    pub matches_only_at_eod: ::std::os::raw::c_char,
  }
  #[test]
  fn bindgen_test_layout_hs_expr_info() {
    const UNINIT: ::std::mem::MaybeUninit<hs_expr_info> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
      ::std::mem::size_of::<hs_expr_info>(),
      12usize,
      concat!("Size of: ", stringify!(hs_expr_info))
    );
    assert_eq!(
      ::std::mem::align_of::<hs_expr_info>(),
      4usize,
      concat!("Alignment of ", stringify!(hs_expr_info))
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).min_width) as usize - ptr as usize },
      0usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_info),
        "::",
        stringify!(min_width)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).max_width) as usize - ptr as usize },
      4usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_info),
        "::",
        stringify!(max_width)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).unordered_matches) as usize - ptr as usize },
      8usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_info),
        "::",
        stringify!(unordered_matches)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).matches_at_eod) as usize - ptr as usize },
      9usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_info),
        "::",
        stringify!(matches_at_eod)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).matches_only_at_eod) as usize - ptr as usize },
      10usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_info),
        "::",
        stringify!(matches_only_at_eod)
      )
    );
  }
  pub type hs_expr_info_t = root::hs_expr_info;
  #[repr(C)]
  #[derive(Debug, Copy, Clone)]
  pub struct hs_expr_ext {
    pub flags: ::std::os::raw::c_ulonglong,
    pub min_offset: ::std::os::raw::c_ulonglong,
    pub max_offset: ::std::os::raw::c_ulonglong,
    pub min_length: ::std::os::raw::c_ulonglong,
    pub edit_distance: ::std::os::raw::c_uint,
    pub hamming_distance: ::std::os::raw::c_uint,
  }
  #[test]
  fn bindgen_test_layout_hs_expr_ext() {
    const UNINIT: ::std::mem::MaybeUninit<hs_expr_ext> = ::std::mem::MaybeUninit::uninit();
    let ptr = UNINIT.as_ptr();
    assert_eq!(
      ::std::mem::size_of::<hs_expr_ext>(),
      40usize,
      concat!("Size of: ", stringify!(hs_expr_ext))
    );
    assert_eq!(
      ::std::mem::align_of::<hs_expr_ext>(),
      8usize,
      concat!("Alignment of ", stringify!(hs_expr_ext))
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).flags) as usize - ptr as usize },
      0usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_ext),
        "::",
        stringify!(flags)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).min_offset) as usize - ptr as usize },
      8usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_ext),
        "::",
        stringify!(min_offset)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).max_offset) as usize - ptr as usize },
      16usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_ext),
        "::",
        stringify!(max_offset)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).min_length) as usize - ptr as usize },
      24usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_ext),
        "::",
        stringify!(min_length)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).edit_distance) as usize - ptr as usize },
      32usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_ext),
        "::",
        stringify!(edit_distance)
      )
    );
    assert_eq!(
      unsafe { ::std::ptr::addr_of!((*ptr).hamming_distance) as usize - ptr as usize },
      36usize,
      concat!(
        "Offset of field: ",
        stringify!(hs_expr_ext),
        "::",
        stringify!(hamming_distance)
      )
    );
  }
  pub type hs_expr_ext_t = root::hs_expr_ext;
  extern "C" {
    pub fn hs_compile(
      expression: *const ::std::os::raw::c_char,
      flags: ::std::os::raw::c_uint,
      mode: ::std::os::raw::c_uint,
      platform: *const root::hs_platform_info_t,
      db: *mut *mut root::hs_database_t,
      error: *mut *mut root::hs_compile_error_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_compile_multi(
      expressions: *const *const ::std::os::raw::c_char,
      flags: *const ::std::os::raw::c_uint,
      ids: *const ::std::os::raw::c_uint,
      elements: ::std::os::raw::c_uint,
      mode: ::std::os::raw::c_uint,
      platform: *const root::hs_platform_info_t,
      db: *mut *mut root::hs_database_t,
      error: *mut *mut root::hs_compile_error_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_compile_ext_multi(
      expressions: *const *const ::std::os::raw::c_char,
      flags: *const ::std::os::raw::c_uint,
      ids: *const ::std::os::raw::c_uint,
      ext: *const *const root::hs_expr_ext_t,
      elements: ::std::os::raw::c_uint,
      mode: ::std::os::raw::c_uint,
      platform: *const root::hs_platform_info_t,
      db: *mut *mut root::hs_database_t,
      error: *mut *mut root::hs_compile_error_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_compile_lit(
      expression: *const ::std::os::raw::c_char,
      flags: ::std::os::raw::c_uint,
      len: usize,
      mode: ::std::os::raw::c_uint,
      platform: *const root::hs_platform_info_t,
      db: *mut *mut root::hs_database_t,
      error: *mut *mut root::hs_compile_error_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_compile_lit_multi(
      expressions: *const *const ::std::os::raw::c_char,
      flags: *const ::std::os::raw::c_uint,
      ids: *const ::std::os::raw::c_uint,
      lens: *const usize,
      elements: ::std::os::raw::c_uint,
      mode: ::std::os::raw::c_uint,
      platform: *const root::hs_platform_info_t,
      db: *mut *mut root::hs_database_t,
      error: *mut *mut root::hs_compile_error_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_free_compile_error(error: *mut root::hs_compile_error_t) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_expression_info(
      expression: *const ::std::os::raw::c_char,
      flags: ::std::os::raw::c_uint,
      info: *mut *mut root::hs_expr_info_t,
      error: *mut *mut root::hs_compile_error_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_expression_ext_info(
      expression: *const ::std::os::raw::c_char,
      flags: ::std::os::raw::c_uint,
      ext: *const root::hs_expr_ext_t,
      info: *mut *mut root::hs_expr_info_t,
      error: *mut *mut root::hs_compile_error_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_populate_platform(platform: *mut root::hs_platform_info_t) -> root::hs_error_t;
  }
  #[repr(C)]
  #[derive(Debug, Copy, Clone)]
  pub struct hs_stream {
    _unused: [u8; 0],
  }
  pub type hs_stream_t = root::hs_stream;
  #[repr(C)]
  #[derive(Debug, Copy, Clone)]
  pub struct hs_scratch {
    _unused: [u8; 0],
  }
  pub type hs_scratch_t = root::hs_scratch;
  pub type match_event_handler = ::std::option::Option<
    unsafe extern "C" fn(
      id: ::std::os::raw::c_uint,
      from: ::std::os::raw::c_ulonglong,
      to: ::std::os::raw::c_ulonglong,
      flags: ::std::os::raw::c_uint,
      context: *mut ::std::os::raw::c_void,
    ) -> ::std::os::raw::c_int,
  >;
  extern "C" {
    pub fn hs_open_stream(
      db: *const root::hs_database_t,
      flags: ::std::os::raw::c_uint,
      stream: *mut *mut root::hs_stream_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_scan_stream(
      id: *mut root::hs_stream_t,
      data: *const ::std::os::raw::c_char,
      length: ::std::os::raw::c_uint,
      flags: ::std::os::raw::c_uint,
      scratch: *mut root::hs_scratch_t,
      onEvent: root::match_event_handler,
      ctxt: *mut ::std::os::raw::c_void,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_close_stream(
      id: *mut root::hs_stream_t,
      scratch: *mut root::hs_scratch_t,
      onEvent: root::match_event_handler,
      ctxt: *mut ::std::os::raw::c_void,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_direct_flush_stream(
      id: *mut root::hs_stream_t,
      scratch: *mut root::hs_scratch_t,
      onEvent: root::match_event_handler,
      ctxt: *mut ::std::os::raw::c_void,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_direct_free_stream(id: *mut root::hs_stream_t) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_direct_reset_stream(id: *mut root::hs_stream_t) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_direct_reset_and_copy_stream(
      to_id: *mut root::hs_stream_t,
      from_id: *const root::hs_stream_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_reset_stream(
      id: *mut root::hs_stream_t,
      flags: ::std::os::raw::c_uint,
      scratch: *mut root::hs_scratch_t,
      onEvent: root::match_event_handler,
      context: *mut ::std::os::raw::c_void,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_copy_stream(
      to_id: *mut *mut root::hs_stream_t,
      from_id: *const root::hs_stream_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_reset_and_copy_stream(
      to_id: *mut root::hs_stream_t,
      from_id: *const root::hs_stream_t,
      scratch: *mut root::hs_scratch_t,
      onEvent: root::match_event_handler,
      context: *mut ::std::os::raw::c_void,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_compress_stream(
      stream: *const root::hs_stream_t,
      buf: *mut ::std::os::raw::c_char,
      buf_space: usize,
      used_space: *mut usize,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_expand_stream(
      db: *const root::hs_database_t,
      stream: *mut *mut root::hs_stream_t,
      buf: *const ::std::os::raw::c_char,
      buf_size: usize,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_reset_and_expand_stream(
      to_stream: *mut root::hs_stream_t,
      buf: *const ::std::os::raw::c_char,
      buf_size: usize,
      scratch: *mut root::hs_scratch_t,
      onEvent: root::match_event_handler,
      context: *mut ::std::os::raw::c_void,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_scan(
      db: *const root::hs_database_t,
      data: *const ::std::os::raw::c_char,
      length: ::std::os::raw::c_uint,
      flags: ::std::os::raw::c_uint,
      scratch: *mut root::hs_scratch_t,
      onEvent: root::match_event_handler,
      context: *mut ::std::os::raw::c_void,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_scan_vector(
      db: *const root::hs_database_t,
      data: *const *const ::std::os::raw::c_char,
      length: *const ::std::os::raw::c_uint,
      count: ::std::os::raw::c_uint,
      flags: ::std::os::raw::c_uint,
      scratch: *mut root::hs_scratch_t,
      onEvent: root::match_event_handler,
      context: *mut ::std::os::raw::c_void,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_alloc_scratch(
      db: *const root::hs_database_t,
      scratch: *mut *mut root::hs_scratch_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_clone_scratch(
      src: *const root::hs_scratch_t,
      dest: *mut *mut root::hs_scratch_t,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_scratch_size(
      scratch: *const root::hs_scratch_t,
      scratch_size: *mut usize,
    ) -> root::hs_error_t;
  }
  extern "C" {
    pub fn hs_free_scratch(scratch: *mut root::hs_scratch_t) -> root::hs_error_t;
  }
}
