use std::str::FromStr;

use nom::{error::FromExternalError, Parser};

use crate::parser_ext::ParserExt;

/// A nom parser that parses any [`FromStr`] type. It uses a recognizer to
/// parse the prefix string that should be parsed via FromStr.
///
/// # Example
///
/// ```
/// use nom::character::complete::digit1;
/// use nom_supreme::parse_from_str;
///
/// fn parse_int(input: &str) -> IResult<&str, i64> {
///     digit1.map_res(|s| s.parse()).parse(input)
/// }
///
/// assert_eq!(parse_int("125 abc"), Ok((" abc", 125)));
/// assert_eq!(parse_int("abc"), Err(123));
///
/// // The recognizer function determines what will be passed to `FromStr`.
/// // in this example, it doesn't accept a leading sign, so this will fail
/// // to parse.
/// assert_eq!(parse_int("-125"), Err(125));
/// ```
pub fn parse_from_str<'a, F, T, E>(recognizer: F) -> impl Parser<&'a str, T, E>
where
    F: Parser<&'a str, &'a str, E> + Sized,
    T: FromStr,
    E: FromExternalError<&'a str, T::Err>,
{
    recognizer.map_res(|value| value.parse())
}
