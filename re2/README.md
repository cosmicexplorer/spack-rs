re2
===

A wrapper of the [re2](https://github.com/google/re2) C++ library to demonstrate a use case for [spack-rs](https://github.com/cosmicexplorer/spack-rs).

*The below syntax guide is reproduced from the `re2` codebase.*

# Regexp Syntax

This module uses the `re2` library and hence supports
its syntax for regular expressions, which is similar to Perl's with
some of the more complicated things thrown away.  In particular,
backreferences and generalized assertions are not available, nor is `\Z`.

See Syntax[^syntax] for the syntax supported by RE2, and a comparison with PCRE and
PERL regexps.

[^syntax]: https://github.com/google/re2/wiki/Syntax

For those not familiar with Perl's regular expressions,
here are some examples of the most commonly used extensions:

- `"hello (\\w+) world"`  -- `\w` matches a "word" character
- `"version (\\d+)"`      -- `\d` matches a digit
- `"hello\\s+world"`      -- `\s` matches any whitespace character
- `"\\b(\\w+)\\b"`        -- `\b` matches non-empty string at word boundary
- `"(?i)hello"`           -- `(?i)` turns on case-insensitive matching
- `"/\\*(.*?)\\*/"`       -- `.*?` matches `.` minimum number of times
  possible

The double backslashes are needed when writing string literals.
However, they should NOT be used when writing raw string literals:

- `r"(hello (\w+) world)"`  -- `\w` matches a "word" character
- `r"(version (\d+))"`      -- `\d` matches a digit
- `r"(hello\s+world)"`      -- `\s` matches any whitespace character
- `r"(\b(\w+)\b)"`          -- `\b` matches non-empty string at word
  boundary
- `r"((?i)hello)"`          -- `(?i)` turns on case-insensitive matching
- `r"(/\*(.*?)\*/)"`        -- `.*?` matches `.` minimum number of times
  possible

When using UTF-8 encoding, case-insensitive matching will perform
simple case folding, not full case folding.

# License
[BSD-3-Clause](./LICENSE), in order to match re2's license.
