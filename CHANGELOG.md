# Changelog

## Unpublished

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
