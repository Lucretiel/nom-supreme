# Changelog

## Unreleased

### Added

- Added `Parser::opt_precedes` and `Parser::opt_preceded_by`
- Added `ContextError`, an improved version of nom's `ContextError` that allows for any kind of context to be attached
- Added `GenericErrorTree`, a version of `ErrorTree` that is generic over the tag, context, and external error types. `ErrorTree` is now a type alias for this type.

### Changed

- Removed all feature flags for now. They may come back later, but probably not until someone cites a desire for nom-supreme in a no-std context.
- `parse_from_str_cut` now supports any input type, like `parse_from_str`.

### Internal

- Upgrade to brownstone 3, for substantial improvement to array parser implementations

### Removed

- Removed the global `parse_from_str` in favor of `ParserExt::parse_from_str`.

## 0.7.0

### Changed

- Add `std` and `error` features
  - `mod error` is gated behind `error` and requires `std`

## 0.6.0

### Changed

- Add compatibility with Nom 7
  - Nom 6 may be dropped in a future release, but for now there haven't been any breaking changes that are relevant to nom-supreme
- The separated_terminated parsers no longer add their own error context
- Minor internal changes to errors

## 0.5.0

### Changed

- `parse_from_str` now works with parsers over any input type.

## 0.4.6

### Added

- Added `array` and `separated_array` to `ParserExt`

### Internal

- Minor implementation refactors
- Add `brownstone` dependency

## 0.4.5

### Added

- Add cutting versions of `Result` combinators, which return `Failure` in the event that the mapping function returns an `Err`.
  - Add `map_res_cut` (thanks @loewenheim)
  - Add `parse_from_str_cut`
- Reexport `ParserExt` at the toplevel

### Fixed

- Fixed some edge case bugs in error handling in `multi`

### Internal

- Various internal refactorings of stuff in `ParserExt`
- Remove `cascade` dependency

## 0.4.4

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
