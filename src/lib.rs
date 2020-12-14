//! A collection of excellent utilities for nom, including:
//!
//! - [`ParserExt`][parser_ext::ParserExt], a trait which makes available
//!   many common nom parser combinators as postfix methods, to complement
//!   those already available on [`nom::Parser`].
//! - [`ErrorTree`][error::ErrorTree], a nom error which retains as much
//!   information and context as possible about the details of the failed
//!   parse, with an excellent indenting formatter for printing these failures.
//!   Integrates with the extra error features of `nom-supreme`.
//! - Improved [`tag`] parsers, which attach the mismatched the error in the
//!   event of a parse failure, similar to
//!   [`char`][nom::character::complete::char].
//! - [`parse_separated_terminated`][multi::parse_separated_terminated], the
//!   perfected folding parser for building parse loops.
//! - [`final_parser`][final_parser::final_parser], which serves as a bridge
//!   between nom-style [`IResult`][nom::IResult] parsers and more typical rust
//!   results. It decorates a nom parser, requiring it to parse all of its
//!   input, not return `Incomplete`. It also uses an
//!   [`ExtractContext`][final_parser::ExtractContext] trait to convert the
//!   error locations in nom errors, which are usually just suffixes of the
//!   input, into more useful locations, such as a line and column number.

#![deny(missing_docs)]

pub mod error;
pub mod final_parser;
mod from_str;
pub mod multi;
pub mod parser_ext;
pub mod tag;

pub use from_str::parse_from_str;
