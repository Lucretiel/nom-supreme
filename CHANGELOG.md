# Changelog

# 0.4.4

### Added

- Add `ExtractContext<E2> for Result<T, E1>`
- Add `collect_separated_terminated`

### Documentation

- Documentation refactoring in `multi`

### Changed

- Internal code style fixes
- Implementation improvements for parsers in `multi`

## 0.4.3

### Added

- Add `with_recognized` combinator to `ParserExt`.

## 0.4.2

### Added

- Implement `ErrorConvert` for `ErrorTree`, enabling its use in bit parsers

### Documentation

- Fix broken links in documentation.
- Fix incorrect example parser in `ErrorTree` doctests.
- Add additional example content to `ErrorTree`.
- Add additional example to `ParserExt::parse_from_str`.

## 0.4.1

### Documentation

- Fixed major typo in `ErrorTree` documentation.

## 0.4.0

### Changed

- Changes to how `ErrorTree` and `Expectation` handle `ErrorKind::Eof`:
  - Because `ErrorKind::Eof` is used interchangeably by some nom parsers to refer to either "expected eof" or "*un*expected eof", we examine the input via InputLength to determine which variant is intended
  - Removed `Expectation::Byte` and `Expectation::AnyChar`, replaced them with `Expectation::Something`.
- Major changes to `ErrorTree::Stack`
  - Now separately represents the context stack and base error as different types.
  - Split `BaseErrorKind` into `BaseErrorKind` and
- `BaseErrorKind::External` now reports the error message on an indented line.

### Internal

- Several updates to interior code, unit tests, and doctests, all related to the `ErrorTree` changes.

### Documentation

- Proofread edits of most of the `nom_supreme::error` docs.
- Added several doctests for `ErrorTree`.

## 0.3.1

### Added

- `ParserExt::parse_from_str`

### Tests

- Add comprehensive unit tests to `parse_separated_terminated`

### Internal

- Bump to [cool_asserts] 1.0.3
- Reimplement `parse_from_str` based on `ParserExt`

## 0.3.0

### Added

- `parse_separated_terminated` now works correctly as documented: it smartly detects when the parser is hanging and bail if necessary.
- `parse_separated_terminated` is now slightly smarter about error cases. If the separator successfully parses a 0-length match, the next item error will include the terminator error as well.

## 0.2.0

### Added

- `ParserExt::by_ref`, which borrows a parser so that it can have combinators applied to it without giving up ownership.

### Changed

- **(BREAKING)** Reworked `ParserExt::delimited_by`:
  - Removed original `delimited_by` in favor of simply using `.preceded_by(..).terminated(..)`.
  - Renamed `ParserExt::delimited_by_both` to `ParserExt::delimited_by`, and added a dedicated parser type, such that it no longer requires `Clone` on the delimiter parser.

### Tests

- Added doctests to all `ParserExt` methods.

### Documentation

- Fixed numerous broken documentation links.

## 0.1.4

### Added

- `.peek()` combinator to `ParserExt`
- `.not()` combinator to `ParserExt`
- `Expectation::AnyChar` and `Expectation::Byte`

### Fixed

- Broken doctests

## 0.1.3

No code changes

### Documentation

- `parse_from_str` example now actually shows `parse_from_str`

## 0.1.2

- Changelog started

[cool_asserts](https://docs.rs/cool_asserts/)
