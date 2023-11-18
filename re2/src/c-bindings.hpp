/* Copyright 2023 Danny McClanahan */
/* SPDX-License-Identifier: BSD-3-Clause */

#ifndef __RE2_C_BINDINGS_H__
#define __RE2_C_BINDINGS_H__

#include "re2/re2.h"
#include "re2/set.h"

namespace re2_c_bindings {

struct StringView {
  const char *data_;
  size_t len_;

  StringView() : data_(nullptr), len_(0) {}
  StringView(const char *data, size_t len) : data_(data), len_(len) {}
  StringView(absl::string_view s) : data_(s.data()), len_(s.length()) {}

  StringView(const StringView &) = default;
  StringView &operator=(const StringView &) = default;

  absl::string_view into_absl_view() const {
    return absl::string_view(data_, len_);
  }
};

struct StringMut {
  char *data_;
  size_t len_;

  StringMut() : data_(nullptr), len_(0) {}
  StringMut(char *data, size_t len) : data_(data), len_(len) {}

  StringMut(const StringMut &) = default;
  StringMut &operator=(const StringMut &) = default;
};

class StringWrapper {
public:
  StringWrapper() : inner_(nullptr) {}
  StringWrapper(StringView s);

  ~StringWrapper() { clear(); }

  StringWrapper(StringWrapper &&rhs) : inner_(rhs.inner_) {}
  StringWrapper(const StringWrapper &) = delete;
  StringWrapper &operator=(const StringWrapper &) = delete;

  void clear();
  void resize(size_t len);

  StringView as_view() const;
  StringMut as_mut_view();

  std::string *get_mutable() {
    if (!inner_) {
      inner_ = new std::string();
    }
    return inner_;
  }

private:
  std::string *inner_;
};

struct NamedGroup {
  StringView name_;
  size_t index_;

  NamedGroup(const NamedGroup &) = default;
  NamedGroup &operator=(const NamedGroup &) = default;
};

class NamedCapturingGroups {
public:
  NamedCapturingGroups(const std::map<int, std::string> &m)
      : named_groups_(m), it_(m.cbegin()) {}

  void deref(NamedGroup *out) const;
  void advance();
  bool completed() const noexcept;

private:
  const std::map<int, std::string> &named_groups_;
  std::map<int, std::string>::const_iterator it_;
};

class RE2Wrapper {
public:
  static void quote_meta(StringView pattern, StringWrapper *out);
  static size_t max_submatch(StringView rewrite);

  RE2Wrapper(StringView pattern, const re2::RE2::Options &options);
  ~RE2Wrapper() { clear(); }

  RE2Wrapper(RE2Wrapper &&rhs) : re_(rhs.re_) {}
  RE2Wrapper(const RE2Wrapper &) = delete;
  RE2Wrapper &operator=(const RE2Wrapper &) = delete;
  RE2Wrapper &operator=(RE2Wrapper &&rhs) {
    clear();
    re_ = rhs.re_;
    return *this;
  }

  void clear();

  StringView pattern() const noexcept;
  const re2::RE2::Options &options() const noexcept;

  re2::RE2::ErrorCode error_code() const noexcept;
  StringView error() const noexcept;
  StringView error_arg() const noexcept;

  size_t num_captures() const noexcept;
  NamedCapturingGroups named_groups() const;

  bool full_match(StringView text) const;
  bool full_match_n(StringView text, StringView captures[], size_t n) const;

  bool partial_match(StringView text) const;
  bool partial_match_n(StringView text, StringView captures[], size_t n) const;

  bool consume(StringView *text) const;
  bool consume_n(StringView *text, StringView captures[], size_t n) const;

  bool find_and_consume(StringView *text) const;
  bool find_and_consume_n(StringView *text, StringView captures[],
                          size_t n) const;

  bool replace(StringWrapper *inout, StringView rewrite) const;
  size_t global_replace(StringWrapper *inout, StringView rewrite) const;
  bool extract(StringView text, StringView rewrite, StringWrapper *out) const;

  bool match_single(StringView text, size_t startpos, size_t endpos,
                    re2::RE2::Anchor re_anchor) const;
  bool match_routine(StringView text, size_t startpos, size_t endpos,
                     re2::RE2::Anchor re_anchor, StringView submatch_args[],
                     size_t nsubmatch) const;

  bool check_rewrite_string(StringView rewrite, StringWrapper *error) const;
  bool vector_rewrite(StringWrapper *out, StringView rewrite,
                      const StringView *vec, size_t veclen) const;

private:
  re2::RE2 *re_;
};

class MatchedSetInfo {
public:
  MatchedSetInfo() : matches_(nullptr) {}

  ~MatchedSetInfo() { clear(); }

  MatchedSetInfo(MatchedSetInfo &&rhs) : matches_(rhs.matches_) {}
  MatchedSetInfo(const MatchedSetInfo &) = delete;
  MatchedSetInfo &operator=(const MatchedSetInfo &) = delete;

  void clear();

  const int *data() const noexcept;
  size_t size() const noexcept;
  size_t capacity() const noexcept;
  void clear_visible_elements();
  void reserve(size_t to);

  std::vector<int> *get_mutable() const {
    if (!matches_) {
      matches_ = new std::vector<int>();
    }
    return matches_;
  }

private:
  mutable std::vector<int> *matches_;
};

class SetWrapper {
public:
  SetWrapper(const re2::RE2::Options &options, re2::RE2::Anchor anchor);
  ~SetWrapper() { clear(); }

  SetWrapper(SetWrapper &&rhs) : set_(rhs.set_) {}
  SetWrapper(const SetWrapper &) = delete;
  SetWrapper &operator=(const SetWrapper &) = delete;

  void clear();

  int add(StringView pattern, StringWrapper *error);
  bool compile();

  bool match_routine(StringView text, MatchedSetInfo *v) const;
  bool match_routine_with_error(StringView text, MatchedSetInfo *v,
                                re2::RE2::Set::ErrorInfo *error_info) const;

private:
  re2::RE2::Set *set_;
};

} /* namespace re2_c_bindings */

#endif /* __RE2_C_BINDINGS_H__ */
