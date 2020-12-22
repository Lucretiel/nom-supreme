# Changelog

## Unpublished

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
