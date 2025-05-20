/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

/// This module stubs out the values from the native bindings that are exposed
/// to the `re2` crate's public API (which are needed to generate docs). They
/// are never used at runtime.
#[allow(warnings)]
pub mod root {
  pub mod re2 {
    pub const RE2_ErrorCode_NoError: RE2_ErrorCode = 0;
    pub const RE2_ErrorCode_ErrorInternal: RE2_ErrorCode = 1;
    pub const RE2_ErrorCode_ErrorBadEscape: RE2_ErrorCode = 2;
    pub const RE2_ErrorCode_ErrorBadCharClass: RE2_ErrorCode = 3;
    pub const RE2_ErrorCode_ErrorBadCharRange: RE2_ErrorCode = 4;
    pub const RE2_ErrorCode_ErrorMissingBracket: RE2_ErrorCode = 5;
    pub const RE2_ErrorCode_ErrorMissingParen: RE2_ErrorCode = 6;
    pub const RE2_ErrorCode_ErrorUnexpectedParen: RE2_ErrorCode = 7;
    pub const RE2_ErrorCode_ErrorTrailingBackslash: RE2_ErrorCode = 8;
    pub const RE2_ErrorCode_ErrorRepeatArgument: RE2_ErrorCode = 9;
    pub const RE2_ErrorCode_ErrorRepeatSize: RE2_ErrorCode = 10;
    pub const RE2_ErrorCode_ErrorRepeatOp: RE2_ErrorCode = 11;
    pub const RE2_ErrorCode_ErrorBadPerlOp: RE2_ErrorCode = 12;
    pub const RE2_ErrorCode_ErrorBadUTF8: RE2_ErrorCode = 13;
    pub const RE2_ErrorCode_ErrorBadNamedCapture: RE2_ErrorCode = 14;
    pub const RE2_ErrorCode_ErrorPatternTooLarge: RE2_ErrorCode = 15;
    pub type RE2_ErrorCode = ::std::os::raw::c_uint;
    pub const RE2_CannedOptions_DefaultOptions: RE2_CannedOptions = 0;
    pub const RE2_CannedOptions_Latin1: RE2_CannedOptions = 1;
    pub const RE2_CannedOptions_POSIX: RE2_CannedOptions = 2;
    pub const RE2_CannedOptions_Quiet: RE2_CannedOptions = 3;
    pub type RE2_CannedOptions = ::std::os::raw::c_uint;
    pub const RE2_Anchor_UNANCHORED: RE2_Anchor = 0;
    pub const RE2_Anchor_ANCHOR_START: RE2_Anchor = 1;
    pub const RE2_Anchor_ANCHOR_BOTH: RE2_Anchor = 2;
    pub type RE2_Anchor = ::std::os::raw::c_uint;
    pub const RE2_Options_Encoding_EncodingUTF8: RE2_Options_Encoding = 1;
    pub const RE2_Options_Encoding_EncodingLatin1: RE2_Options_Encoding = 2;
    pub type RE2_Options_Encoding = ::std::os::raw::c_uint;
    pub const RE2_Options_kDefaultMaxMem: ::std::os::raw::c_int = 8388608;
    pub const RE2_Set_ErrorKind_kNoError: RE2_Set_ErrorKind = 0;
    pub const RE2_Set_ErrorKind_kNotCompiled: RE2_Set_ErrorKind = 1;
    pub const RE2_Set_ErrorKind_kOutOfMemory: RE2_Set_ErrorKind = 2;
    pub const RE2_Set_ErrorKind_kInconsistent: RE2_Set_ErrorKind = 3;
    pub type RE2_Set_ErrorKind = ::std::os::raw::c_uint;
    #[derive(Debug, Copy, Clone)]
    pub struct RE2_Set_ErrorInfo;
    #[derive(Debug, Copy, Clone)]
    pub struct RE2_Options;
    #[derive(Debug, Copy, Clone)]
    pub struct RE2;
    #[derive(Debug, Copy, Clone)]
    pub struct RE2_Set;
  }
  pub mod re2_c_bindings {
    #[derive(Debug, Copy, Clone)]
    pub struct StringView;
    #[derive(Debug, Copy, Clone)]
    pub struct StringMut;
    #[derive(Debug, Copy, Clone)]
    pub struct NamedGroup;
    #[derive(Debug, Copy, Clone)]
    pub struct MatchedSetInfo;
    #[derive(Debug, Copy, Clone)]
    pub struct RE2Wrapper;
    #[derive(Debug, Copy, Clone)]
    pub struct SetWrapper;
    #[derive(Debug, Copy, Clone)]
    pub struct StringWrapper;
    #[derive(Debug, Copy, Clone)]
    pub struct NamedCapturingGroups;
    #[derive(Debug, Copy, Clone)]
    pub struct StringSet;
    #[derive(Debug, Copy, Clone)]
    pub struct FilteredRE2Wrapper;
  }
}
