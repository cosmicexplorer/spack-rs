/* Copyright 2022-2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#include "c-bindings.hpp"

namespace re2_c_bindings {

StringWrapper::StringWrapper() : inner_() {}
StringWrapper::StringWrapper(StringView s) : inner_(s.data_, s.len_) {}
StringWrapper::~StringWrapper() {}

StringView StringWrapper::as_view() const {
  return StringView(inner_.data(), inner_.size());
}

StringWrapper RE2Wrapper::quote_meta(const StringView pattern) {
  return StringWrapper(
      std::move(re2::RE2::QuoteMeta(pattern.into_absl_view())));
}

RE2Wrapper::RE2Wrapper(StringView pattern, const re2::RE2::Options &options)
    : re_(pattern.into_absl_view(), options) {}

RE2Wrapper::~RE2Wrapper() {}

re2::RE2::ErrorCode RE2Wrapper::error_code() const noexcept {
  return re_.error_code();
}

StringView RE2Wrapper::pattern() const noexcept {
  absl::string_view sv(re_.pattern());
  return StringView(sv);
}

StringView RE2Wrapper::error() const noexcept {
  absl::string_view sv(re_.error());
  return StringView(sv);
}

StringView RE2Wrapper::error_arg() const noexcept {
  absl::string_view sv(re_.error_arg());
  return StringView(sv);
}

static bool parse_string_view(const char *data, size_t len, void *dest) {
  StringView *dest_sv = reinterpret_cast<StringView *>(dest);
  dest_sv->data_ = data;
  dest_sv->len_ = len;
  return true;
}

bool RE2Wrapper::full_match_n(StringView text, StringView args[],
                              const size_t n) const {
  std::vector<re2::RE2::Arg> argv_args;
  std::vector<const re2::RE2::Arg *> argv;

  for (size_t i = 0; i < n; ++i) {
    argv_args.emplace_back(&args[i], parse_string_view);
    argv.push_back(&argv_args.at(i));
  }

  const auto tv = text.into_absl_view();
  const int n2 = n;
  return re2::RE2::FullMatchN(tv, re_, argv.data(), n2);
}

bool RE2Wrapper::partial_match_n(StringView text, StringView args[],
                                 const size_t n) const {
  std::vector<re2::RE2::Arg> argv_args;
  std::vector<const re2::RE2::Arg *> argv;

  for (size_t i = 0; i < n; ++i) {
    argv_args.emplace_back(&args[i], parse_string_view);
    argv.push_back(&argv_args.at(i));
  }

  const auto tv = text.into_absl_view();
  const int n2 = n;
  return re2::RE2::PartialMatchN(tv, re_, argv.data(), n2);
}

} /* namespace re2_c_bindings */
