//! Enhanced tag parser for nom.
//!
//! This module introduces a new trait, [`TagError`], and variants of `tag`
//! and `tag_case_insensitive` that can use the trait to add to an error the
//! specific tag that was expected. This allows the error message to report
//! something like `Expected tag: "true"` instead of just `Error: Tag`.

use nom::error::{Error, ErrorKind, ParseError, VerboseError};

/// Similar to [`FromExternalError`][nom::error::FromExternalError] and
/// [`ContextError`][nom::error::ContextError], this trait allows a parser to
/// create an error representing an unmatched tag. This allows error messages
/// to produce more useful context about what went wrong.
pub trait TagError<I, T>: Sized {
    /// Create an error from an expected tag at a location.
    fn from_tag(input: I, tag: T) -> Self;

    /// As above, but for a case insensitive tag. By default this just
    /// calls [`from_tag`][Self::from_tag]
    fn from_tag_no_case(input: I, tag: T) -> Self {
        Self::from_tag(input, tag)
    }
}

impl<I, T> TagError<I, T> for () {
    fn from_tag(_input: I, _tag: T) {}
}

impl<I, T> TagError<I, T> for (I, ErrorKind) {
    fn from_tag(input: I, _tag: T) -> Self {
        (input, ErrorKind::Tag)
    }
}

impl<I, T> TagError<I, T> for Error<I> {
    fn from_tag(input: I, _tag: T) -> Self {
        Error::new(input, ErrorKind::Tag)
    }
}

impl<I, T> TagError<I, T> for VerboseError<I> {
    fn from_tag(input: I, _tag: T) -> Self {
        VerboseError::from_error_kind(input, ErrorKind::Tag)
    }
}

/// Complete input version of enhanced `tag` parsers
pub mod complete {
    use nom::{Compare, CompareResult, Err, IResult, InputLength, InputTake};

    use super::TagError;

    /// Parser recognizing a fixed pattern, called a tag. If the front of the
    /// input data matches the `tag`, that part of the input will be returned.
    /// Records the tag in the error in the event of a parse failure via
    /// [`TagError`].
    ///
    /// # Example
    ///
    /// ```
    /// # use nom::{IResult, Err, Needed};
    /// use cool_asserts::assert_matches;
    /// use nom_supreme::tag::complete::tag;
    /// use nom_supreme::error::{ErrorTree, BaseErrorKind, Expectation};
    ///
    /// fn parse_hello(s: &str) -> IResult<&str, &str, ErrorTree<&str>> {
    ///     tag("hello")(s)
    /// }
    ///
    /// assert_matches!(
    ///     parse_hello("hello, world!"),
    ///     Ok((", world!", "hello")),
    /// );
    ///
    /// assert_matches!(
    ///     parse_hello("something"),
    ///     Err(Err::Error(ErrorTree::Base {
    ///         location: "something",
    ///         kind: BaseErrorKind::Expected(Expectation::Tag("hello")),
    ///     }))
    /// );
    ///
    /// assert_matches!(
    ///     parse_hello("hel"),
    ///     Err(Err::Error(ErrorTree::Base {
    ///         location: "hel",
    ///         kind: BaseErrorKind::Expected(Expectation::Tag("hello")),
    ///     }))
    /// );
    /// ```
    pub fn tag<T, I, E>(tag: T) -> impl Clone + Fn(I) -> IResult<I, I, E>
    where
        T: InputLength + Clone,
        I: InputTake + Compare<T>,
        E: TagError<I, T>,
    {
        let tag_len = tag.input_len();

        move |input: I| match input.compare(tag.clone()) {
            CompareResult::Ok => Ok(input.take_split(tag_len)),
            _ => Err(Err::Error(E::from_tag(input, tag.clone()))),
        }
    }

    /// Parser recognizing a fixed pattern, called a tag. If the front of the
    /// input data matches the `tag`, case insensitively, that part of the
    /// input will be returned. Records the tag in the error in the event of a
    /// parse failure via [`TagError`].
    ///
    /// # Example
    ///
    /// ```
    /// # use nom::{IResult, Err, Needed};
    /// use cool_asserts::assert_matches;
    /// use nom_supreme::tag::complete::tag_no_case;
    /// use nom_supreme::error::{ErrorTree, BaseErrorKind, Expectation};
    ///
    /// fn parse_hello(s: &str) -> IResult<&str, &str, ErrorTree<&str>> {
    ///     tag_no_case("hello")(s)
    /// }
    ///
    /// assert_matches!(
    ///     parse_hello("HELLO, WORLD!"),
    ///     Ok((", WORLD!", "HELLO")),
    /// );
    ///
    /// assert_matches!(
    ///     parse_hello("something"),
    ///     Err(Err::Error(ErrorTree::Base {
    ///         location: "something",
    ///         kind: BaseErrorKind::Expected(Expectation::Tag("hello")),
    ///     }))
    /// );
    ///
    /// assert_matches!(
    ///     parse_hello("HEL"),
    ///     Err(Err::Error(ErrorTree::Base {
    ///         location: "HEL",
    ///         kind: BaseErrorKind::Expected(Expectation::Tag("hello")),
    ///     }))
    /// );
    /// ```
    pub fn tag_no_case<T, I, E>(tag: T) -> impl Clone + Fn(I) -> IResult<I, I, E>
    where
        T: InputLength + Clone,
        I: InputTake + Compare<T>,
        E: TagError<I, T>,
    {
        move |input: I| match input.compare_no_case(tag.clone()) {
            CompareResult::Ok => Ok(input.take_split(tag.input_len())),
            _ => Err(Err::Error(E::from_tag_no_case(input, tag.clone()))),
        }
    }
}

/// Streaming version of enhanced `tag` parsers.
pub mod streaming {
    use nom::{Compare, CompareResult, Err, IResult, InputLength, InputTake, Needed};

    use super::TagError;

    /// Parser recognizing a fixed pattern, called a tag. If the front of the
    /// input data matches the `tag`, that part of the input will be returned.
    /// Records the tag in the error in the event of a parse failure via
    /// [`TagError`]. If there is only a partial match, returns
    /// [`Err::Incomplete`][nom::Err::Incomplete].
    ///
    /// # Example
    ///
    /// ```
    /// # use nom::{IResult, Err, Needed};
    /// use cool_asserts::assert_matches;
    /// use nom_supreme::tag::streaming::tag;
    /// use nom_supreme::error::{ErrorTree, BaseErrorKind, Expectation};
    ///
    /// fn parse_hello(s: &str) -> IResult<&str, &str, ErrorTree<&str>> {
    ///     tag("hello")(s)
    /// }
    ///
    /// assert_matches!(
    ///     parse_hello("hello, world!"),
    ///     Ok((", world!", "hello")),
    /// );
    ///
    /// assert_matches!(
    ///     parse_hello("something"),
    ///     Err(Err::Error(ErrorTree::Base {
    ///         location: "something",
    ///         kind: BaseErrorKind::Expected(Expectation::Tag("hello")),
    ///     }))
    /// );
    ///
    /// assert_matches!(
    ///     parse_hello("hel"),
    ///     Err(Err::Incomplete(Needed::Size(n))) if n.get() == 2,
    /// );
    /// ```
    pub fn tag<T, I, E>(tag: T) -> impl Clone + Fn(I) -> IResult<I, I, E>
    where
        T: InputLength + Clone,
        I: InputLength + InputTake + Compare<T>,
        E: TagError<I, T>,
    {
        let tag_len = tag.input_len();

        move |input: I| match input.compare(tag.clone()) {
            CompareResult::Ok => Ok(input.take_split(tag_len)),
            CompareResult::Incomplete => {
                Err(Err::Incomplete(Needed::new(tag_len - input.input_len())))
            }
            CompareResult::Error => Err(Err::Error(E::from_tag(input, tag.clone()))),
        }
    }

    /// Parser recognizing a fixed pattern, called a tag. If the front of the
    /// input data matches the `tag`, case insensitively, that part of the
    /// input will be returned. Records the tag in the error in the event of a
    /// parse failure via [`TagError`]. If there is only a partial match,
    /// returns [`Err::Incomplete`][[nom::Err::Incomplete]].
    ///
    /// # Example
    ///
    /// ```
    /// # use nom::{IResult, Err, Needed};
    /// use cool_asserts::assert_matches;
    /// use nom_supreme::tag::streaming::tag_no_case;
    /// use nom_supreme::error::{ErrorTree, BaseErrorKind, Expectation};
    ///
    /// fn parse_hello(s: &str) -> IResult<&str, &str, ErrorTree<&str>> {
    ///     tag_no_case("hello")(s)
    /// }
    ///
    /// assert_matches!(
    ///     parse_hello("HELLO, WORLD!"),
    ///     Ok((", WORLD!", "HELLO")),
    /// );
    ///
    /// assert_matches!(
    ///     parse_hello("something"),
    ///     Err(Err::Error(ErrorTree::Base {
    ///         location: "something",
    ///         kind: BaseErrorKind::Expected(Expectation::Tag("hello")),
    ///     }))
    /// );
    ///
    /// assert_matches!(
    ///     parse_hello("HEL"),
    ///     Err(Err::Incomplete(Needed::Size(n))) if n.get() == 2,
    /// );
    /// ```
    pub fn tag_no_case<T, I, E>(tag: T) -> impl Clone + Fn(I) -> IResult<I, I, E>
    where
        T: InputLength + Clone,
        I: InputLength + InputTake + Compare<T>,
        E: TagError<I, T>,
    {
        let tag_len = tag.input_len();

        move |input: I| match input.compare_no_case(tag.clone()) {
            CompareResult::Ok => Ok(input.take_split(tag_len)),
            CompareResult::Incomplete => {
                Err(Err::Incomplete(Needed::new(tag_len - input.input_len())))
            }
            CompareResult::Error => Err(Err::Error(E::from_tag_no_case(input, tag.clone()))),
        }
    }
}
