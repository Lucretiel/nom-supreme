//! An error type, [`ErrorTree`], designed to retain much more useful
//! information about parse failures than the built-in nom error types.
//! Requires the `error` feature to be enabled.

use std::{
    error::Error,
    fmt::{self, Debug, Display, Formatter, Write},
};

use indent_write::fmt::IndentWriter;
use joinery::JoinableIterator;
use nom::{
    error::{ErrorKind as NomErrorKind, FromExternalError, ParseError},
    ErrorConvert, InputLength,
};

use crate::{
    final_parser::{ExtractContext, RecreateContext},
    tag::TagError,
    ContextError,
};

/// Enum for generic things that can be expected by nom parsers
///
/// Certain nom parsers (think [`digit1`], [`tag`], or [`space1`]) are "base
/// level" in the sense that, rather than combining subparsers, they scan for a
/// specific character or specific kind of character. This enum tracks the
/// different kinds of things that can be expected by these base parses.
///
/// Printing an expectation via [`Display`] will only include the thing that
/// was expected, in a form suitable for being prefixed with "expected" or
/// suffixed with "was expected".
///
/// This enum is non-exhaustive; it is intended to represent everything parse
/// errors where we know *specifically* what was expected. For instance,
/// [`take_while`] cannot create an [`Expectation`], because it can't
/// meaningfully report what its subparser is expecting.
///
/// [`digit1`]: nom::character::complete::digit1
/// [`tag`]: crate::tag::complete::tag
/// [`space1`]: nom::character::complete::space1
/// [`take_while`]: nom::bytes::complete::take_while
#[non_exhaustive]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Expectation<T> {
    /// A tag was expected.
    Tag(T),

    /// A specific character was expected.
    Char(char),

    /// An ASCII letter (`[a-zA-Z]`) was expected.
    Alpha,

    /// A decimal digit (`[0-9]`) was expected.
    Digit,

    /// A hexadecimal digit (`[0-9a-fA-F]`) was expected.
    HexDigit,

    /// An octal digit (`[0-7]`) was expected.
    OctDigit,

    /// An alphanumeric character (`[0-9a-zA-Z]`) was expected.
    AlphaNumeric,

    /// A space or tab was expected.
    Space,

    /// A space, tab, newline, or carriage return was expected.
    Multispace,

    /// `"\r\n"` was expected.
    CrLf,

    /// Eof was expected.
    Eof,

    /// Expected something; ie, not Eof.
    Something,
}

impl<T: Debug> Display for Expectation<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            Expectation::Tag(ref tag) => write!(f, "{:?}", tag),
            Expectation::Char(c) => write!(f, "{:?}", c),
            Expectation::Alpha => write!(f, "an ascii letter"),
            Expectation::Digit => write!(f, "an ascii digit"),
            Expectation::HexDigit => write!(f, "a hexadecimal digit"),
            Expectation::OctDigit => write!(f, "an octal digit"),
            Expectation::AlphaNumeric => write!(f, "an ascii alphanumeric character"),
            Expectation::Space => write!(f, "a space or tab"),
            Expectation::Multispace => write!(f, "whitespace"),
            Expectation::Eof => write!(f, "eof"),
            Expectation::CrLf => write!(f, "CRLF"),
            Expectation::Something => write!(f, "not eof"),
        }
    }
}

/// These are the different specific things that can go wrong at a particular
/// location during a nom parse. Many of these are collected into an
/// [`ErrorTree`].
///
/// - `T` is the tag type, such as &'static str.
/// - `E` is the external error type, such as `Box<dyn Error>`.
#[derive(Debug)]
pub enum BaseErrorKind<T, E> {
    /// Something specific was expected, such as a specific
    /// [character][Expectation::Char] or any [digit](Expectation::Digit).
    /// See [`Expectation`] for details.
    Expected(Expectation<T>),

    /// A nom parser failed.
    Kind(NomErrorKind),

    /// An error outside of nom occurred during parsing; for instance, as a
    /// result of an error during [`map_res`].
    ///
    /// [`map_res`]: crate::parser_ext::ParserExt::map_res
    // Design note: I've gone back and forth on whether or not to exclude the
    // ErrorKind from this variant. Right now I'm doing so, because it seems
    // like in practice it's *always* MapRes.
    External(E),
}

impl<T: Debug, E: Display> Display for BaseErrorKind<T, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            BaseErrorKind::Expected(ref expectation) => write!(f, "expected {}", expectation),
            BaseErrorKind::External(ref err) => {
                writeln!(f, "external error:")?;
                let mut f = IndentWriter::new("  ", f);
                write!(f, "{}", err)
            }
            BaseErrorKind::Kind(kind) => write!(f, "error in {:?}", kind),
        }
    }
}

/// Context that can appear in a [stack][GenericErrorTree::Stack], above a base
/// [`ErrorTree`]. Stack contexts are attached by parser combinators to errors
/// from their subparsers during stack unwinding.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum StackContext<C> {
    /// A nom combinator attached an [`ErrorKind`][NomErrorKind] as context
    /// for a subparser error.
    Kind(NomErrorKind),

    /// The [`context`][crate::parser_ext::ParserExt::context] combinator
    /// attached a message as context for a subparser error.
    Context(C),
}

impl<C: Debug> Display for StackContext<C> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match *self {
            StackContext::Kind(kind) => write!(f, "while parsing {:?}", kind),
            StackContext::Context(ref ctx) => write!(f, "in section {:?}", ctx),
        }
    }
}

/// A comprehensive tree of nom errors describing a parse failure.
///
/// This Error type is designed to be [`VerboseError`]`++`. While
/// [`VerboseError`] can represent a *stack* of errors, this type can represent
/// a full tree. In addition to representing a particular specific parse error,
/// it can also represent a stack of nested error contexts (for instance, as
/// provided by [`context`][crate::ParserExt::context]), or a list of
/// alternatives that were all tried individually by [`alt`][nom::branch::alt]
/// and all failed.
///
/// In general, the design goal for this type is to discard as little useful
/// information as possible. That being said, many [`ErrorKind`] variants add
/// very little useful contextual information to error traces; for example,
/// [`ErrorKind::Alt`] doesn't add any interesting context to an
/// [`ErrorTree::Alt`], and its presence in a stack precludes merging together
/// adjacent sets of [`ErrorTree::Alt`] siblings.
///
/// # Examples
///
/// ## Base parser errors
///
/// An `ErrorTree::Base` is an error that occurred at the "bottom" of the stack,
/// from a parser looking for 1 specific kind of thing.
///
/// ```rust
/// use cool_asserts::assert_matches;
/// use nom::{Parser, Err};
/// use nom::character::complete::{digit1, char};
/// use nom_supreme::error::{ErrorTree, BaseErrorKind, StackContext, Expectation};
/// use nom_supreme::parser_ext::ParserExt;
///
/// let err: Err<ErrorTree<&str>> = digit1.parse("abc").unwrap_err();
///
/// assert_matches!(err, Err::Error(ErrorTree::Base{
///     location: "abc",
///     kind: BaseErrorKind::Expected(Expectation::Digit),
/// }));
///
/// let err: Err<ErrorTree<&str>> = char('a').and(char('b')).parse("acb").unwrap_err();
///
/// assert_matches!(err, Err::Error(ErrorTree::Base{
///     location: "cb",
///     kind: BaseErrorKind::Expected(Expectation::Char('b')),
/// }));
/// ```
///
/// ## Stacks
///
/// An [`ErrorTree::Stack`] is created when a parser combinator—typically
/// [`context`]—attaches additional error context to a subparser error. It can
/// have any [`ErrorTree`] at the base of the stack.
///
/// ```rust
/// use cool_asserts::assert_matches;
/// use nom::{Parser, Err};
/// use nom::character::complete::{alpha1, space1, char,};
/// use nom::sequence::{separated_pair, delimited};
/// use nom_supreme::parser_ext::ParserExt;
/// use nom_supreme::error::{ErrorTree, BaseErrorKind, StackContext, Expectation};
///
/// // Parse a single identifier, defined as just a string of letters.
/// let identifier = alpha1.context("identifier");
///
/// // Parse a pair of identifiers, separated by whitespace
/// let identifier_pair = separated_pair(identifier, space1, identifier)
///     .context("identifier pair");
///
/// // Parse a pair of identifiers in parenthesis.
/// let mut parenthesized = delimited(char('('), identifier_pair, char(')'))
///     .context("parenthesized");
///
/// let err: Err<ErrorTree<&str>> = parenthesized.parse("(abc 123)").unwrap_err();
///
/// assert_matches!(err, Err::Error(ErrorTree::Stack {
///     base,
///     contexts,
/// }) => {
///     assert_matches!(*base, ErrorTree::Base {
///         location: "123)",
///         kind: BaseErrorKind::Expected(Expectation::Alpha)
///     });
///
///     assert_eq!(contexts, [
///         ("123)", StackContext::Context("identifier")),
///         ("abc 123)", StackContext::Context("identifier pair")),
///         ("(abc 123)", StackContext::Context("parenthesized")),
///     ]);
/// });
/// ```
///
/// ## Alternatives
///
/// An [`ErrorTree::Alt`] is created when a series of parsers are all tried,
/// and all of them fail. Most commonly this will happen via the
/// [`alt`][nom::branch::alt] combinator or the equivalent [`.or`] postfix
/// combinator. When all of these subparsers fail, their errors (each
/// individually their own `ErrorTree`) are aggregated into an
/// [`ErrorTree::Alt`], indicating that "any one of these things were
/// expected."
///
/// ```rust
/// use cool_asserts::assert_matches;
/// use nom::{Parser, Err};
/// use nom::branch::alt;
/// use nom_supreme::error::{ErrorTree, BaseErrorKind, StackContext, Expectation};
/// use nom_supreme::parser_ext::ParserExt;
/// use nom_supreme::tag::complete::tag;
///
/// let parse_bool = alt((
///     tag("true").value(true),
///     tag("false").value(false),
/// ));
///
/// let mut parse_null_bool = alt((
///     parse_bool.map(Some),
///     tag("null").value(None),
/// ));
///
/// assert_eq!(parse_null_bool.parse("true").unwrap(), ("", Some(true)));
/// assert_eq!(parse_null_bool.parse("false").unwrap(), ("", Some(false)));
/// assert_eq!(parse_null_bool.parse("null").unwrap(), ("", None));
///
/// let err: Err<ErrorTree<&str>> = parse_null_bool.parse("123").unwrap_err();
///
/// // This error communicates to the caller that any one of "true", "false",
/// // or "null" was expected at that location.
/// assert_matches!(err, Err::Error(ErrorTree::Alt(choices)) => {
///     assert_matches!(choices.as_slice(), [
///         ErrorTree::Base {
///             location: "123",
///             kind: BaseErrorKind::Expected(Expectation::Tag("true"))},
///         ErrorTree::Base {
///             location: "123",
///             kind: BaseErrorKind::Expected(Expectation::Tag("false"))},
///         ErrorTree::Base {
///             location: "123",
///             kind: BaseErrorKind::Expected(Expectation::Tag("null"))},
///     ])
/// });
/// ```
///
/// ## Contexts and Alternatives
///
/// Because [`Stack`] and [`Alt`] recursively contain [`ErrorTree`] errors from
/// subparsers, they can be can combined to create error trees of arbitrary
/// complexity.
///
/// ```rust
/// use cool_asserts::assert_matches;
/// use nom::{Parser, Err};
/// use nom::branch::alt;
/// use nom_supreme::error::{ErrorTree, BaseErrorKind, StackContext, Expectation};
/// use nom_supreme::parser_ext::ParserExt;
/// use nom_supreme::tag::complete::tag;
///
/// let parse_bool = alt((
///     tag("true").value(true),
///     tag("false").value(false),
/// )).context("bool");
///
/// let mut parse_null_bool = alt((
///     parse_bool.map(Some),
///     tag("null").value(None).context("null"),
/// )).context("null or bool");
///
/// assert_eq!(parse_null_bool.parse("true").unwrap(), ("", Some(true)));
/// assert_eq!(parse_null_bool.parse("false").unwrap(), ("", Some(false)));
/// assert_eq!(parse_null_bool.parse("null").unwrap(), ("", None));
///
/// let err: Err<ErrorTree<&str>> = parse_null_bool.parse("123").unwrap_err();
///
/// assert_matches!(err, Err::Error(ErrorTree::Stack{base, contexts}) => {
///     assert_eq!(contexts, [("123", StackContext::Context("null or bool"))]);
///     assert_matches!(*base, ErrorTree::Alt(choices) => {
///         assert_matches!(&choices[0], ErrorTree::Stack{base, contexts} => {
///             assert_eq!(contexts, &[("123", StackContext::Context("bool"))]);
///             assert_matches!(&**base, ErrorTree::Alt(choices) => {
///                 assert_matches!(&choices[0], ErrorTree::Base {
///                     location: "123",
///                     kind: BaseErrorKind::Expected(Expectation::Tag("true"))
///                 });
///                 assert_matches!(&choices[1], ErrorTree::Base {
///                     location: "123",
///                     kind: BaseErrorKind::Expected(Expectation::Tag("false"))
///                 });
///            });
///         });
///         assert_matches!(&choices[1], ErrorTree::Stack{base, contexts} => {
///             assert_eq!(contexts, &[("123", StackContext::Context("null"))]);
///             assert_matches!(&**base, ErrorTree::Base {
///                 location: "123",
///                 kind: BaseErrorKind::Expected(Expectation::Tag("null"))
///             });
///         });
///     });
/// });
/// ```
///
/// # Display formatting
///
/// TODO WRITE THIS SECTION
///
/// [`.or`]: nom::Parser::or
/// [`Alt`]: ErrorTree::Alt
/// [`context`]: nom::error::context
/// [`ErrorKind::Alt`]: nom::error::ErrorKind::Alt
/// [`ErrorKind`]: nom::error::ErrorKind
/// [`Stack`]: GenericErrorTree::Stack
/// [`VerboseError`]: nom::error::VerboseError
/// [`ErrorTree::Alt`]: GenericErrorTree::Alt
pub type ErrorTree<I> =
    GenericErrorTree<I, &'static str, &'static str, Box<dyn Error + Send + Sync + 'static>>;

/// Generic version of [`ErrorTree`], which allows for arbitrary `Tag`, `Context`,
/// and `ExternalError` types. See [`ErrorTree`] for more extensive docs and
/// examples.
///
/// - `Tag` is typically something like `&'static str` or `&'static [u8]`.
/// - `Context` is typically `&'static str`, and it must be in order to
///   interoperate with nom's [`context`][nom::error::context] combinator.
///   `nom-supreme` provides a more generic [`.context`][crate::ParserExt::context]
///   combinator that allows for any kind of context to be attached to an error.
/// - `Error` can usually be nothing, as it's unusual for nom parsers to
///   require external errors. `Box<dyn Error + Send + Sync + 'static>` is
///   a common catch-all.
#[derive(Debug)]
pub enum GenericErrorTree<Location, Tag, Context, ExternalError> {
    /// A specific error event at a specific location. Often this will indicate
    /// that something like a tag or character was expected at that location.
    Base {
        /// The location of this error in the input
        location: Location,

        /// The specific error that occurred
        kind: BaseErrorKind<Tag, ExternalError>,
    },

    /// A stack indicates a chain of error contexts was provided. The stack
    /// should be read "backwards"; that is, errors *earlier* in the `Vec`
    /// occurred "sooner" (deeper in the call stack).
    Stack {
        /// The original error
        base: Box<Self>,

        /// The stack of contexts attached to that error
        contexts: Vec<(Location, StackContext<Context>)>,
    },

    /// A series of parsers were tried at the same location (for instance, via
    /// the [`alt`](nom::branch::alt) combinator) and all of them failed. All
    /// of the errors in this set are "siblings".
    Alt(Vec<Self>),
    // TODO: in a future version of nom-supreme, elaborate on the specific
    // type combinations here. For instance:
    // - Alt can only contain Stack or Base
    // - Stack has a single Base or Alt, followed by a series of contexts
    //   (Context or Kind)
}

impl<I, T, C, E> GenericErrorTree<I, T, C, E> {
    /// Helper for `map_locations`. Because it operates recursively, this
    /// method uses an `&mut impl FnMut`, which can be reborrowed.
    fn map_locations_ref<I2>(
        self,
        convert_location: &mut impl FnMut(I) -> I2,
    ) -> GenericErrorTree<I2, T, C, E> {
        // TODO: does the recursive nature of this function present a potential
        // security risk? Consider replacing it with a breadth-first algorithm,
        // or capping the maximum recursion depth. Note, though, that recursion
        // only happens when alternating between different *kinds* of
        // ErrorTree; nested groups of Alt or Stack are flattened.
        match self {
            GenericErrorTree::Base { location, kind } => GenericErrorTree::Base {
                location: convert_location(location),
                kind,
            },
            GenericErrorTree::Stack { base, contexts } => GenericErrorTree::Stack {
                base: Box::new(base.map_locations_ref(convert_location)),
                contexts: contexts
                    .into_iter()
                    .map(|(location, context)| (convert_location(location), context))
                    .collect(),
            },
            GenericErrorTree::Alt(siblings) => GenericErrorTree::Alt(
                siblings
                    .into_iter()
                    .map(|err| err.map_locations_ref(convert_location))
                    .collect(),
            ),
        }
    }

    /// Convert all of the locations in this error using some kind of mapping
    /// function. This is intended to help add additional context that may not
    /// have been available when the nom parsers were running, such as line
    /// and column numbers.
    pub fn map_locations<I2>(
        self,
        mut convert_location: impl FnMut(I) -> I2,
    ) -> GenericErrorTree<I2, T, C, E> {
        self.map_locations_ref(&mut convert_location)
    }
}

impl<I: Display, T: Debug, C: Debug, E: Display> Display for GenericErrorTree<I, T, C, E> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            GenericErrorTree::Base { location, kind } => write!(f, "{} at {:#}", kind, location),
            GenericErrorTree::Stack { contexts, base } => {
                contexts.iter().rev().try_for_each(|(location, context)| {
                    writeln!(f, "{} at {:#},", context, location)
                })?;

                base.fmt(f)
            }
            GenericErrorTree::Alt(siblings) => {
                writeln!(f, "one of:")?;
                let mut f = IndentWriter::new("  ", f);
                write!(f, "{}", siblings.iter().join_with(", or\n"))
            }
        }
    }
}

impl<I: Display + Debug, T: Debug, C: Debug, E: Display + Debug> Error
    for GenericErrorTree<I, T, C, E>
{
}

impl<I: InputLength, T, C, E> ParseError<I> for GenericErrorTree<I, T, C, E> {
    /// Create a new error at the given position. Interpret `kind` as an
    /// [`Expectation`] if possible, to give a more informative error message.
    fn from_error_kind(location: I, kind: NomErrorKind) -> Self {
        let kind = match kind {
            NomErrorKind::Alpha => BaseErrorKind::Expected(Expectation::Alpha),
            NomErrorKind::Digit => BaseErrorKind::Expected(Expectation::Digit),
            NomErrorKind::HexDigit => BaseErrorKind::Expected(Expectation::HexDigit),
            NomErrorKind::OctDigit => BaseErrorKind::Expected(Expectation::OctDigit),
            NomErrorKind::AlphaNumeric => BaseErrorKind::Expected(Expectation::AlphaNumeric),
            NomErrorKind::Space => BaseErrorKind::Expected(Expectation::Space),
            NomErrorKind::MultiSpace => BaseErrorKind::Expected(Expectation::Multispace),
            NomErrorKind::CrLf => BaseErrorKind::Expected(Expectation::CrLf),

            // Problem: ErrorKind::Eof is used interchangeably by various nom
            // parsers to mean either "expected Eof" or "expected NOT eof". See
            // https://github.com/Geal/nom/issues/1259. For now, we examine the
            // input string to guess what the likely intention is.
            NomErrorKind::Eof => match location.input_len() {
                // The input is at Eof, which means that this refers to an
                // *unexpected* eof.
                0 => BaseErrorKind::Expected(Expectation::Something),

                // The input is *not* at eof, which means that this refers to
                // an *expected* eof.
                _ => BaseErrorKind::Expected(Expectation::Eof),
            },
            kind => BaseErrorKind::Kind(kind),
        };

        GenericErrorTree::Base { location, kind }
    }

    /// Combine an existing error with a new one. This is how error context is
    /// accumulated when backtracing. "other" is the original error, and the
    /// inputs new error from higher in the call stack.
    ///
    /// If `other` is already an `GenericErrorTree::Stack`, the context is added to
    /// the stack; otherwise, a new stack is created, with `other` at the root.
    fn append(location: I, kind: NomErrorKind, other: Self) -> Self {
        let context = (location, StackContext::Kind(kind));

        match other {
            // Don't create a stack of [ErrorKind::Alt, GenericErrorTree::Alt(..)]
            alt @ GenericErrorTree::Alt(..) if kind == NomErrorKind::Alt => alt,

            // This is already a stack, so push on to it
            GenericErrorTree::Stack { contexts, base } => GenericErrorTree::Stack {
                base,
                contexts: express!(contexts.push(context)),
            },

            // This isn't a stack; create a new stack
            base => GenericErrorTree::Stack {
                base: Box::new(base),
                contexts: vec![context],
            },
        }
    }

    /// Create an error indicating an expected character at a given position
    fn from_char(location: I, character: char) -> Self {
        GenericErrorTree::Base {
            location,
            kind: BaseErrorKind::Expected(Expectation::Char(character)),
        }
    }

    /// Combine two errors from branches of alt. If either or both errors are
    /// already [`GenericErrorTree::Alt`], the different error sets are merged;
    /// otherwise, a new [`GenericErrorTree::Alt`] is created, containing both
    /// `self` and `other`.
    fn or(self, other: Self) -> Self {
        // For now we assume that there's no need to try and preserve
        // left-to-right ordering of alternatives.
        let siblings = match (self, other) {
            (GenericErrorTree::Alt(siblings1), GenericErrorTree::Alt(siblings2)) => {
                match siblings1.capacity() >= siblings2.capacity() {
                    true => express!(siblings1.extend(siblings2)),
                    false => express!(siblings2.extend(siblings1)),
                }
            }
            (GenericErrorTree::Alt(siblings), err) | (err, GenericErrorTree::Alt(siblings)) => {
                express!(siblings.push(err))
            }
            (err1, err2) => vec![err1, err2],
        };

        GenericErrorTree::Alt(siblings)
    }
}

impl<I, T, C, E> ContextError<I, C> for GenericErrorTree<I, T, C, E> {
    fn add_context(location: I, ctx: C, other: Self) -> Self {
        let context = (location, StackContext::Context(ctx));

        match other {
            // This is already a stack, so push on to it
            GenericErrorTree::Stack { contexts, base } => GenericErrorTree::Stack {
                base,
                contexts: express!(contexts.push(context)),
            },

            // This isn't a stack, create a new stack
            base => GenericErrorTree::Stack {
                base: Box::new(base),
                contexts: vec![context],
            },
        }
    }
}

impl<I, T, E> nom::error::ContextError<I> for GenericErrorTree<I, T, &'static str, E> {
    fn add_context(location: I, ctx: &'static str, other: Self) -> Self {
        ContextError::add_context(location, ctx, other)
    }
}

impl<I, T, C, E, E2> FromExternalError<I, E2> for GenericErrorTree<I, T, C, E>
where
    E: From<E2>,
{
    /// Create an error from a given external error, such as from FromStr
    fn from_external_error(location: I, _kind: NomErrorKind, e: E2) -> Self {
        GenericErrorTree::Base {
            location,
            kind: BaseErrorKind::External(e.into()),
        }
    }
}

impl<I, T: AsRef<[u8]>, C, E> TagError<I, T> for GenericErrorTree<I, T, C, E> {
    fn from_tag(location: I, tag: T) -> Self {
        GenericErrorTree::Base {
            location,
            kind: BaseErrorKind::Expected(match tag.as_ref() {
                b"\r\n" => Expectation::CrLf,
                _ => Expectation::Tag(tag),
            }),
        }
    }
}

impl<I, T, C, E> ErrorConvert<GenericErrorTree<(I, usize), T, C, E>>
    for GenericErrorTree<I, T, C, E>
{
    fn convert(self) -> GenericErrorTree<(I, usize), T, C, E> {
        self.map_locations(|location| (location, 0))
    }
}

impl<I, T, C, E> ErrorConvert<GenericErrorTree<I, T, C, E>>
    for GenericErrorTree<(I, usize), T, C, E>
{
    fn convert(self) -> GenericErrorTree<I, T, C, E> {
        self.map_locations(move |(location, _offset)| location)
    }
}

impl<I, I2, T, C, E> ExtractContext<I, GenericErrorTree<I2, T, C, E>>
    for GenericErrorTree<I, T, C, E>
where
    I: Clone,
    I2: RecreateContext<I>,
{
    fn extract_context(self, original_input: I) -> GenericErrorTree<I2, T, C, E> {
        self.map_locations(move |location| I2::recreate_context(original_input.clone(), location))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use nom::{
        bits::{bits, complete::take},
        sequence::tuple,
        IResult, Parser,
    };

    type BitInput<'a> = (&'a [u8], usize);

    fn parse_bool_bit(input: (&[u8], usize)) -> IResult<BitInput, bool, ErrorTree<BitInput>> {
        take(1usize).map(|bit: u8| bit != 0).parse(input)
    }

    type Byte = (bool, bool, bool, bool, bool, bool, bool, bool);

    /// Parse 8 bits
    fn parse_bits(input: &[u8]) -> IResult<&[u8], Byte, ErrorTree<&[u8]>> {
        bits(tuple((
            parse_bool_bit,
            parse_bool_bit,
            parse_bool_bit,
            parse_bool_bit,
            parse_bool_bit,
            parse_bool_bit,
            parse_bool_bit,
            parse_bool_bit,
        )))
        .parse(input)
    }

    /// Test that ErrorTree can be used with a bits parser, which requires
    /// ErrorConvert
    #[test]
    fn error_tree_bits() {
        let values = [0b1010_1111, 10];
        let (tail, result) = parse_bits(&values).unwrap();

        assert_eq!(tail, &[10]);
        assert_eq!(result, (true, false, true, false, true, true, true, true));
    }
}
