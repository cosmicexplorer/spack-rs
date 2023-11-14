/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#ifndef __RE2_C_BINDINGS_H__
#define __RE2_C_BINDINGS_H__

#include "re2/re2.h"

namespace re2_c_bindings {

struct StringView {
  const char *data_;
  size_t len_;

  StringView() : data_(nullptr), len_(0) {}
  StringView(const char *data, size_t len) : data_(data), len_(len) {}
  StringView(absl::string_view s) : data_(s.data()), len_(s.length()) {}

  StringView(const StringView &rhs) = default;
  StringView &operator=(const StringView &rhs) = default;

  absl::string_view into_absl_view() const {
    return absl::string_view(data_, len_);
  }
};

class StringWrapper {
public:
  StringWrapper();
  StringWrapper(StringView s);
  StringWrapper(std::string *s) : inner_(s) {}

  StringWrapper(StringWrapper &&rhs) : inner_(rhs.inner_) {}
  StringWrapper(const StringWrapper &) = delete;
  StringWrapper &operator=(const StringWrapper &) = delete;

  void clear();

  StringView as_view() const;
  std::string *get_mutable() {
    if (inner_ == nullptr) {
      inner_ = new std::string();
    }
    return inner_;
  }

private:
  std::string *inner_;
};

class RE2Wrapper {
public:
  static void quote_meta(StringView pattern, StringWrapper* out);

  RE2Wrapper(StringView pattern, const re2::RE2::Options &options);

  void clear();

  re2::RE2::ErrorCode error_code() const noexcept;

  StringView pattern() const noexcept;
  StringView error() const noexcept;
  StringView error_arg() const noexcept;

  size_t num_captures() const noexcept;

  bool full_match(StringView text) const;
  bool full_match_n(StringView text, StringView captures[], size_t n) const;
  bool partial_match(StringView text) const;
  bool partial_match_n(StringView text, StringView captures[], size_t n) const;

private:
  re2::RE2 *re_;
};

} /* namespace re2_c_bindings */

#endif /* __RE2_C_BINDINGS_H__ */
