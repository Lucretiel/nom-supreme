use std::str::FromStr;

use nom::{error::FromExternalError, Parser};

use crate::parser_ext::ParserExt;

/// A nom parser that parses any [`FromStr`] type. It uses a recognizer to
/// parse the prefix string that should be parsed via FromStr.
///
/// # Example
///
/// ```
/// # use nom::{IResult, Err, character::complete::digit1, Parser, error::{Error, ErrorKind}};
/// use nom_supreme::{parse_from_str, parser_ext::ParserExt};
///
/// fn parse_int(input: &str) -> IResult<&str, i64> {
///     parse_from_str(digit1).parse(input)
/// }
///
/// assert_eq!(parse_int("125 abc"), Ok((" abc", 125)));
/// assert_eq!(parse_int("abc"), Err(Err::Error(Error{input: "abc", code: ErrorKind::Digit})));
///
/// // The recognizer function determines what will be passed to `FromStr`.
/// // in this example, it doesn't accept a leading sign, so this will fail
/// // to parse.
/// assert_eq!(parse_int("-125"),  Err(Err::Error(Error{input: "-125", code: ErrorKind::Digit})));
/// ```
pub fn parse_from_str<'a, F, T, E>(recognizer: F) -> impl Parser<&'a str, T, E>
where
    F: Parser<&'a str, &'a str, E> + Sized,
    T: FromStr,
    E: FromExternalError<&'a str, T::Err>,
{
    recognizer.parse_from_str()
}
