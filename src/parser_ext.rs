//! Extensions to the nom [`Parser`][nom::Parser] trait which add postfix
//! versions of the common combinators. See [`ParserExt`] for details.

use std::{marker::PhantomData, ops::RangeTo, str::FromStr};

use nom::{
    error::{ContextError, ErrorKind as NomErrorKind, FromExternalError, ParseError},
    Err as NomErr, InputLength, Offset, Parser, Slice,
};

/// No-op function that typechecks that its argument is a parser. Used to
/// ensure there are no accidentally missing type bounds on the `ParserExt`
/// methods
#[inline(always)]
fn must_be_a_parser<I, O, E, P: Parser<I, O, E>>(parser: P) -> P {
    parser
}

/// Additional postfix parser combinators, as a complement to [`Parser`].
/// Mostly these are postfix versions of the combinators in [`nom::combinator`]
/// and [`nom::sequence`], with some additional combinators original to
/// `nom-supreme`.
///
/// Compatibility note: it is expected that eventually many of these postfix
/// methods will eventually be added directly to the [`Parser`] trait. It will
/// therefore *not* be considered a compatibility break to remove those methods
/// from [`ParserExt`], *if* they have the same name and signature.
pub trait ParserExt<I, O, E>: Parser<I, O, E> + Sized {
    /// Borrow a parser. This allows building parser combinators while still
    /// retaining ownership of the original parser. This is necessary because
    /// `impl<T: Parser> Parser for &mut T` is impossible due to conflicts
    /// with `impl<T: FnMut> Parser for T`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Hello");
    ///
    /// let mut subparser = parser.by_ref().terminated(tag(", World"));
    ///
    /// assert_eq!(subparser.parse("Hello, World!"), Ok(("!", "Hello")));
    /// assert_eq!(
    ///     subparser.parse("Hello"),
    ///     Err(Err::Error(Error{input: "", code: ErrorKind::Tag}))
    /// );
    ///
    /// // We still have ownership of the original parser
    ///
    /// assert_eq!(parser.parse("Hello, World!"), Ok((", World!", "Hello")));
    /// assert_eq!(parser.parse("Hello"), Ok(("", "Hello")));
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn by_ref(&mut self) -> RefParser<Self> {
        must_be_a_parser(RefParser { parser: self })
    }

    /// Create a parser that must consume all of the input, or else return an
    /// error.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Hello").all_consuming();
    ///
    /// assert_eq!(parser.parse("Hello"), Ok(("", "Hello")));
    /// assert_eq!(
    ///     parser.parse("World"),
    ///     Err(Err::Error(Error{input: "World", code: ErrorKind::Tag}))
    /// );
    /// assert_eq!(
    ///     parser.parse("Hello World"),
    ///     Err(Err::Error(Error{input: " World", code: ErrorKind::Eof}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn all_consuming(self) -> AllConsuming<Self>
    where
        I: InputLength,
        E: ParseError<I>,
    {
        must_be_a_parser(AllConsuming { parser: self })
    }

    /// Create a parser that transforms `Incomplete` into `Error`.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::streaming::tag;
    ///
    /// let mut parser = tag("Hello").complete();
    ///
    /// assert_eq!(parser.parse("Hello"), Ok(("", "Hello")));
    /// assert_eq!(
    ///     parser.parse("World"),
    ///     Err(Err::Error(Error{input: "World", code: ErrorKind::Tag}))
    /// );
    /// assert_eq!(
    ///     parser.parse("Hel"),
    ///     Err(Err::Error(Error{input: "Hel", code: ErrorKind::Complete}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn complete(self) -> Complete<Self>
    where
        I: Clone,
        E: ParseError<I>,
    {
        must_be_a_parser(Complete { parser: self })
    }

    /// Create a parser that transforms `Error` into `Failure`. This will
    /// end the parse immediately, even if there are other branches that
    /// could occur.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Hello").cut();
    ///
    /// assert_eq!(parser.parse("Hello"), Ok(("", "Hello")));
    /// assert_eq!(
    ///     parser.parse("World"),
    ///     Err(Err::Failure(Error{input: "World", code: ErrorKind::Tag}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn cut(self) -> Cut<Self> {
        must_be_a_parser(Cut { parser: self })
    }

    /// Create a parser that applies a mapping function `func` to the output
    /// of the subparser. Any errors from `func` will be transformed into
    /// parse errors via [`FromExternalError`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::alphanumeric1;
    /// use nom_supreme::parser_ext::ParserExt;
    ///
    /// let mut parser = alphanumeric1.map_res(|s: &str| s.parse());
    ///
    /// assert_eq!(parser.parse("10 abc"), Ok((" abc", 10)));
    /// assert_eq!(
    ///     parser.parse("<===>"),
    ///     Err(Err::Error(Error{input: "<===>", code: ErrorKind::AlphaNumeric})),
    /// );
    /// assert_eq!(
    ///     parser.parse("abc abc"),
    ///     Err(Err::Error(Error{input: "abc abc", code: ErrorKind::MapRes})),
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn map_res<F, O2, E2>(self, func: F) -> MapRes<Self, F, O, E2>
    where
        F: FnMut(O) -> Result<O2, E2>,
        E: FromExternalError<I, E2>,
        I: Clone,
    {
        must_be_a_parser(MapRes {
            parser: self,
            func,
            phantom: PhantomData,
        })
    }

    /// Create a parser that applies a mapping function `func` to the output
    /// of the subparser. Any errors from `func` will be transformed into
    /// parse failures via [`FromExternalError`]. This will
    /// end the parse immediately, even if there are other branches that
    /// could occur.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::alphanumeric1;
    /// use nom_supreme::parser_ext::ParserExt;
    ///
    /// let mut parser = alphanumeric1.map_res_cut(|s: &str| s.parse());
    ///
    /// assert_eq!(parser.parse("10 abc"), Ok((" abc", 10)));
    /// assert_eq!(
    ///     parser.parse("<===>"),
    ///     Err(Err::Error(Error{input: "<===>", code: ErrorKind::AlphaNumeric})),
    /// );
    /// assert_eq!(
    ///     parser.parse("abc abc"),
    ///     Err(Err::Failure(Error{input: "abc abc", code: ErrorKind::MapRes})),
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn map_res_cut<F, O2, E2>(self, func: F) -> MapResCut<Self, F, O, E2>
    where
        F: FnMut(O) -> Result<O2, E2>,
        E: FromExternalError<I, E2>,
        I: Clone,
    {
        must_be_a_parser(MapResCut {
            parser: self,
            func,
            phantom: PhantomData,
        })
    }

    /// Make this parser optional; if it fails to parse, instead it returns
    /// `None` with the input in the original position.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser, IResult};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// fn parser(input: &str) -> IResult<&str, Option<&str>> {
    ///     tag("Hello").opt().parse(input)
    /// }
    ///
    /// assert_eq!(parser.parse("Hello, World"), Ok((", World", Some("Hello"))));
    /// assert_eq!(parser.parse("World"), Ok(("World", None)));
    ///
    /// let mut parser = tag("Hello").cut().opt();
    /// assert_eq!(
    ///     parser.parse("World"),
    ///     Err(Err::Failure(Error{input: "World", code: ErrorKind::Tag}))
    /// )
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn opt(self) -> Optional<Self>
    where
        I: Clone,
    {
        must_be_a_parser(Optional { parser: self })
    }

    /// Replace this parser's output with the entire input that was consumed
    /// by the parser.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::space1;
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Hello").delimited_by(space1).recognize();
    ///
    /// assert_eq!(parser.parse("   Hello   World!"), Ok(("World!", "   Hello   ")));
    /// assert_eq!(
    ///     parser.parse("Hello"),
    ///     Err(Err::Error(Error{input: "Hello", code: ErrorKind::Space}))
    /// )
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn recognize(self) -> Recognize<Self, O>
    where
        I: Clone + Slice<RangeTo<usize>> + Offset,
    {
        must_be_a_parser(Recognize {
            parser: self.with_recognized(),
            phantom: PhantomData,
        })
    }

    /// Return the parsed value, but also return the entire input that was
    /// consumed by the parse
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::space1;
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Hello").delimited_by(space1).with_recognized();
    ///
    /// assert_eq!(parser.parse("   Hello   World!"), Ok(("World!", ("   Hello   ", "Hello"))));
    /// assert_eq!(
    ///     parser.parse("Hello"),
    ///     Err(Err::Error(Error{input: "Hello", code: ErrorKind::Space}))
    /// )
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn with_recognized(self) -> WithRecognized<Self>
    where
        I: Clone + Slice<RangeTo<usize>> + Offset,
    {
        must_be_a_parser(WithRecognized { parser: self })
    }

    /// Replace this parser's output with a clone of `value` every time it
    /// finishes successfully.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::branch::alt;
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    /// use nom_supreme::error::{ErrorTree, BaseErrorKind, Expectation};
    ///
    ///
    /// let mut parser = alt((
    ///     tag("true").value(true),
    ///     tag("false").value(false),
    /// ));
    ///
    /// assert_eq!(parser.parse("true abc").unwrap(), (" abc", true));
    /// assert_eq!(parser.parse("false abc").unwrap(), (" abc", false));
    ///
    /// // ErrorTree gives much better error reports for alt and tag.
    /// let err = parser.parse("null").unwrap_err();
    /// let choices = match err {
    ///     Err::Error(ErrorTree::Alt(choices)) => choices,
    ///     _ => panic!("Unexpected error {:?}", err)
    /// };
    /// assert!(matches!(
    ///     choices.as_slice(),
    ///     [
    ///         ErrorTree::Base {
    ///             kind: BaseErrorKind::Expected(Expectation::Tag("true")),
    ///             location: "null",
    ///         },
    ///         ErrorTree::Base {
    ///             kind: BaseErrorKind::Expected(Expectation::Tag("false")),
    ///             location: "null",
    ///         },
    ///     ]
    /// ))
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn value<T: Clone>(self, value: T) -> Value<T, Self, O> {
        must_be_a_parser(Value {
            parser: self,
            value,
            phantom: PhantomData,
        })
    }

    /// Require the output of this parser to pass a verifier function, or
    /// else return a parse error.
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::alpha1;
    /// use nom_supreme::parser_ext::ParserExt;
    ///
    /// let mut parser = alpha1.verify(|s: &&str| s.len() == 5);
    ///
    /// assert_eq!(parser.parse("Hello"), Ok(("", "Hello")));
    /// assert_eq!(parser.parse("Hello, World"), Ok((", World", "Hello")));
    /// assert_eq!(
    ///     parser.parse("abc"),
    ///     Err(Err::Error(Error{input: "abc", code: ErrorKind::Verify}))
    /// );
    /// assert_eq!(
    ///     parser.parse("abcabcabc"),
    ///     Err(Err::Error(Error{input: "abcabcabc", code: ErrorKind::Verify}))
    /// );
    /// assert_eq!(
    ///     parser.parse("123"),
    ///     Err(Err::Error(Error{input: "123", code: ErrorKind::Alpha}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn verify<F>(self, verifier: F) -> Verify<Self, F>
    where
        F: Fn(&O) -> bool,
        I: Clone,
        E: ParseError<I>,
    {
        must_be_a_parser(Verify {
            parser: self,
            verifier,
        })
    }

    /// Add some context to the parser. This context will be added to any
    /// errors that are returned from the parser via [`ContextError`].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{VerboseError, ErrorKind, VerboseErrorKind};
    /// use nom::sequence::separated_pair;
    /// use nom::character::complete::space1;
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = separated_pair(
    ///     tag("Hello").context("hello"),
    ///     space1,
    ///     tag("World").context("world"),
    /// )
    /// .context("hello world");
    ///
    /// assert_eq!(parser.parse("Hello World"), Ok(("", ("Hello", "World"))));
    /// assert_eq!(
    ///     parser.parse("Hel"),
    ///     Err(Err::Error(VerboseError {errors: vec![
    ///         ("Hel", VerboseErrorKind::Nom(ErrorKind::Tag)),
    ///         ("Hel", VerboseErrorKind::Context("hello")),
    ///         ("Hel", VerboseErrorKind::Context("hello world")),
    ///     ]}))
    /// );
    /// assert_eq!(
    ///     parser.parse("Hello"),
    ///     Err(Err::Error(VerboseError {errors: vec![
    ///         ("", VerboseErrorKind::Nom(ErrorKind::Space)),
    ///         ("Hello", VerboseErrorKind::Context("hello world")),
    ///     ]}))
    /// );
    /// assert_eq!(
    ///     parser.parse("Hello Wor"),
    ///     Err(Err::Error(VerboseError {errors: vec![
    ///         ("Wor", VerboseErrorKind::Nom(ErrorKind::Tag)),
    ///         ("Wor", VerboseErrorKind::Context("world")),
    ///         ("Hello Wor", VerboseErrorKind::Context("hello world")),
    ///     ]}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn context(self, context: &'static str) -> Context<Self>
    where
        E: ContextError<I>,
        I: Clone,
    {
        must_be_a_parser(Context {
            context,
            parser: self,
        })
    }

    /// Add a terminator parser. The terminator will run after this parser,
    /// returning any errors, but its output will otherwise be discarded.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Hello").terminated(tag(" World"));
    ///
    /// assert_eq!(parser.parse("Hello World!"), Ok(("!", "Hello")));
    /// assert_eq!(
    ///     parser.parse("Hello"),
    ///     Err(Err::Error(Error{input: "", code: ErrorKind::Tag}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn terminated<F, O2>(self, terminator: F) -> Terminated<Self, F, O2>
    where
        F: Parser<I, O2, E>,
    {
        must_be_a_parser(Terminated {
            parser: self,
            terminator,
            phantom: PhantomData,
        })
    }

    /// Make this parser precede another one. The successor parser will run
    /// after this one succeeds, and the successor's output will be returned.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::digit1;
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Value: ").precedes(digit1);
    ///
    /// assert_eq!(parser.parse("Value: 25;"), Ok((";", "25")));
    /// assert_eq!(
    ///     parser.parse("Value: "),
    ///     Err(Err::Error(Error{input: "", code: ErrorKind::Digit}))
    /// );
    /// assert_eq!(
    ///     parser.parse("25"),
    ///     Err(Err::Error(Error{input: "25", code: ErrorKind::Tag}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn precedes<F, O2>(self, successor: F) -> Preceded<F, Self, O>
    where
        F: Parser<I, O2, E>,
    {
        must_be_a_parser(successor.preceded_by(self))
    }

    /// Make this parser preceded by another one. The `prefix` will run first,
    /// and if it succeeds, its output will be discard and this parser will
    /// be run.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::digit1;
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = digit1.preceded_by(tag("Value: "));
    ///
    /// assert_eq!(parser.parse("Value: 25;"), Ok((";", "25")));
    /// assert_eq!(
    ///     parser.parse("Value: "),
    ///     Err(Err::Error(Error{input: "", code: ErrorKind::Digit}))
    /// );
    /// assert_eq!(
    ///     parser.parse("25"),
    ///     Err(Err::Error(Error{input: "25", code: ErrorKind::Tag}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn preceded_by<F, O2>(self, prefix: F) -> Preceded<Self, F, O2>
    where
        F: Parser<I, O2, E>,
    {
        must_be_a_parser(Preceded {
            parser: self,
            prefix,
            phantom: PhantomData,
        })
    }

    /// Make this parser delimited, requiring a `delimiter` as both a prefix and
    /// a suffix. The output of the delimiters is discarded.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::{char, digit1};
    /// use nom_supreme::parser_ext::ParserExt;
    ///
    /// let mut parser = digit1.delimited_by(char('\''));
    ///
    /// assert_eq!(parser.parse("'123' '456'"), Ok((" '456'", "123")));
    /// assert_eq!(
    ///     parser.parse("'' ''"),
    ///     Err(Err::Error(Error{input: "' ''", code: ErrorKind::Digit}))
    /// );
    /// assert_eq!(
    ///     parser.parse("'123 '"),
    ///     Err(Err::Error(Error{input: " '", code: ErrorKind::Char}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn delimited_by<D, O2>(self, delimiter: D) -> Delimited<Self, D, O2>
    where
        D: Parser<I, O2, E>,
    {
        must_be_a_parser(Delimited {
            parser: self,
            delimiter,
            phantom: PhantomData,
        })
    }

    /// Make this parser peeking: it runs normally but consumes no input.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Hello").peek();
    ///
    /// assert_eq!(parser.parse("Hello World"), Ok(("Hello World", "Hello")));
    /// assert_eq!(
    ///     parser.parse("World"),
    ///     Err(Err::Error(Error{input: "World", code: ErrorKind::Tag}))
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn peek(self) -> Peek<Self>
    where
        I: Clone,
    {
        must_be_a_parser(Peek { parser: self })
    }

    /// Make this parser a negative lookahead: it will succeed if the subparser
    /// fails, and fail if the subparser succeeds.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = tag("Hello").not();
    ///
    /// assert_eq!(parser.parse("World"), Ok(("World", ())));
    /// assert_eq!(
    ///     parser.parse("Hello World"),
    ///     Err(Err::Error(Error{input: "Hello World", code: ErrorKind::Not})),
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn not(self) -> Not<Self, O>
    where
        I: Clone,
        E: ParseError<I>,
    {
        must_be_a_parser(Not {
            parser: self,
            phantom: PhantomData,
        })
    }

    /// Create a parser that parses something via [`FromStr`], using this
    /// parser as a recognizer for the string to pass to
    /// [`from_str`][FromStr::from_str].
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser, IResult};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::digit1;
    /// use nom_supreme::parser_ext::ParserExt;
    ///
    /// let mut parser = digit1.parse_from_str();
    ///
    /// assert_eq!(parser.parse("123 abc"), Ok((" abc", 123)));
    /// assert_eq!(
    ///     parser.parse("abc"),
    ///     Err(Err::Error(Error{input: "abc", code: ErrorKind::Digit})),
    /// );
    /// ```
    ///
    /// # Parse error example
    ///
    /// If the [`FromStr`] parser fails, the error is recoverable from via
    /// [`FromExternalError`]. In general, though, it's better practice to
    /// ensure your recognizer won't allow invalid strings to be forwarded to
    /// the [`FromStr`] parser
    ///
    /// ```rust
    /// use std::num::ParseIntError;
    /// use cool_asserts::assert_matches;
    /// # use nom::{Err, Parser, IResult};
    /// # use nom::error::{ErrorKind};
    /// use nom::character::complete::alphanumeric1;
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::error::{ErrorTree, BaseErrorKind};
    ///
    /// let mut parser = alphanumeric1.parse_from_str();
    ///
    /// assert_matches!(parser.parse("123 abc"), Ok((" abc", 123)));
    /// assert_matches!(
    ///     parser.parse("abc"),
    ///     Err(Err::Error(ErrorTree::Base{
    ///         location: "abc",
    ///         kind: BaseErrorKind::External(err),
    ///     })) => {
    ///         let _err: &ParseIntError = err.downcast_ref().unwrap();
    ///     },
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn parse_from_str<'a, T>(self) -> FromStrParser<Self, T>
    where
        Self: Parser<&'a str, &'a str, E>,
        T: FromStr,
        E: FromExternalError<&'a str, T::Err>,
    {
        must_be_a_parser(FromStrParser {
            parser: self,
            phantom: PhantomData,
        })
    }

    /// Create a parser that parses something via [`FromStr`], using this
    /// parser as a recognizer for the string to pass to
    /// [`from_str`][FromStr::from_str]. This parser transforms any errors
    /// from [`FromStr`] into [`Err::Failure`][NomErr::Failure], which will
    /// end the overall parse immediately, even if there are other branches
    /// that could be tried.
    ///
    /// # Example
    ///
    /// ```rust
    /// # use nom::{Err, Parser, IResult};
    /// # use nom::error::{Error, ErrorKind};
    /// use nom::character::complete::alphanumeric1;
    /// use nom_supreme::parser_ext::ParserExt;
    ///
    /// let mut parser = alphanumeric1.parse_from_str_cut();
    ///
    /// assert_eq!(parser.parse("123 abc"), Ok((" abc", 123)));
    /// assert_eq!(
    ///     parser.parse("<===>"),
    ///     Err(Err::Error(Error{input: "<===>", code: ErrorKind::AlphaNumeric})),
    /// );
    /// assert_eq!(
    ///     parser.parse("abc"),
    ///     Err(Err::Failure(Error{input: "abc", code: ErrorKind::MapRes})),
    /// );
    /// ```
    ///
    /// # Parse error example
    ///
    /// If the [`FromStr`] parser fails, the error is recoverable from via
    /// [`FromExternalError`]. In general, though, it's better practice to
    /// ensure your recognizer won't allow invalid strings to be forwarded to
    /// the [`FromStr`] parser
    ///
    /// ```rust
    /// use std::num::ParseIntError;
    /// use cool_asserts::assert_matches;
    /// # use nom::{Err, Parser, IResult};
    /// # use nom::error::{ErrorKind};
    /// use nom::character::complete::alphanumeric1;
    /// use nom_supreme::parser_ext::ParserExt;
    /// use nom_supreme::error::{ErrorTree, BaseErrorKind};
    ///
    /// let mut parser = alphanumeric1.parse_from_str_cut();
    ///
    /// assert_matches!(parser.parse("123 abc"), Ok((" abc", 123)));
    /// assert_matches!(
    ///     parser.parse("abc"),
    ///     Err(Err::Failure(ErrorTree::Base{
    ///         location: "abc",
    ///         kind: BaseErrorKind::External(err),
    ///     })) => {
    ///         let _err: &ParseIntError = err.downcast_ref().unwrap();
    ///     },
    /// );
    /// ```
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn parse_from_str_cut<'a, T>(self) -> FromStrCutParser<Self, T>
    where
        Self: Parser<&'a str, &'a str, E>,
        T: FromStr,
        E: FromExternalError<&'a str, T::Err>,
    {
        must_be_a_parser(FromStrCutParser {
            parser: self,
            phantom: PhantomData,
        })
    }

    /// Create a parser that parses a fixed-size array by running this parser
    /// in a loop.
    ///
    /// The returned parser implements [`Parser`] generically over any
    /// `const N: usize`, which means it can be used to parse arrays of any
    /// length
    ///
    /// # Example
    ///
    /// ```rust
    /// use cool_asserts::assert_matches;
    /// use nom::character::complete::digit1;
    /// # use nom::{Parser, Err, IResult};
    /// # use nom::error::{ErrorKind, Error};
    /// use nom_supreme::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = digit1
    ///     .terminated(tag(", "))
    ///     .parse_from_str()
    ///     .array();
    ///
    /// assert_matches!(parser.parse("123, 456, 789, abc"), Ok(("789, abc", [123, 456])));
    /// assert_matches!(parser.parse("123, 456, 789, abc"), Ok(("abc", [123, 456, 789])));
    ///
    /// let res: Result<(&str, [u16; 4]), Err<Error<&str>>> = parser.parse("123, 456, 789, abc");
    /// assert_matches!(
    ///     res,
    ///     Err(Err::Error(Error{input: "abc", code: ErrorKind::Digit}))
    /// );
    /// ```
    ///
    /// Note that this parser does not attach any additional context to the
    /// error in the event of a parser; consider using [`context`] on the
    /// item parser or array parser to add additional information about where
    /// in the input there was a parse failure.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn array(self) -> ArrayParser<Self> {
        ArrayParser { parser: self }
    }

    /// Create a parser that parses a fixed-size array by running this parser
    /// in a loop, parsing a separator in between each element.
    ///
    /// The returned parser implements [`Parser`] generically over any
    /// `const N: usize`, which means it can be used to parse arrays of any
    /// length
    ///
    /// # Example
    ///
    /// ```rust
    /// use std::net::{Ipv4Addr, SocketAddrV4};
    /// use cool_asserts::assert_matches;
    /// use nom::character::complete::{char, digit1};
    /// # use nom::{Parser, Err, IResult};
    /// # use nom::error::{ErrorKind, Error};
    /// use nom_supreme::ParserExt;
    /// use nom_supreme::tag::complete::tag;
    ///
    /// let mut parser = digit1
    ///     .parse_from_str()
    ///     .separated_array(char('.'))
    ///     .map(Ipv4Addr::from)
    ///     .terminated(char(':'))
    ///     .and(digit1.parse_from_str())
    ///     .map(|(ip, port)| SocketAddrV4::new(ip, port));
    ///
    /// let (_tail, socket_addr) = parser.parse("192.168.0.1:80").unwrap();
    /// assert_eq!(socket_addr.ip().octets(), [192, 168, 0, 1]);
    /// assert_eq!(socket_addr.port(), 80);
    ///
    /// assert_matches!(
    ///     parser.parse("192.168.0.abc:80"),
    ///     Err(Err::Error(Error{input: "abc:80", code: ErrorKind::Digit})),
    /// );
    ///
    /// assert_matches!(
    ///     parser.parse("192.168.0.1"),
    ///     Err(Err::Error(Error{input: "", code: ErrorKind::Char})),
    /// );
    ///
    /// assert_matches!(
    ///     parser.parse("192.168.0.1000:80"),
    ///     Err(Err::Error(Error{input: "1000:80", code: ErrorKind::MapRes})),
    /// );
    ///
    /// assert_matches!(
    ///     parser.parse("192.168.10abc"),
    ///     Err(Err::Error(Error{input: "abc", code: ErrorKind::Char})),
    /// );
    /// ```
    ///
    /// Note that this parser does not attach any additional context to the
    /// error in the event of a parser; consider using [`context`] on the
    /// item parser or array parser to add additional information about where
    /// in the input there was a parse failure.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn separated_array<F, O2>(self, separator: F) -> SeparatedArrayParser<Self, F, O2>
    where
        F: Parser<I, O2, E>,
    {
        SeparatedArrayParser {
            parser: self,
            separator,
            phantom: PhantomData,
        }
    }
}

impl<I, O, E, P> ParserExt<I, O, E> for P where P: Parser<I, O, E> {}

/// Parser wrapping a mutable reference to a subparser.
#[derive(Debug)]
pub struct RefParser<'a, P> {
    parser: &'a mut P,
}

impl<'a, I, O, E, P> Parser<I, O, E> for RefParser<'a, P>
where
    P: Parser<I, O, E>,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O, E> {
        self.parser.parse(input)
    }
}

/// Parser which returns an error if the subparser didn't consume the whole
/// input.
#[derive(Debug, Clone, Copy)]
pub struct AllConsuming<P> {
    parser: P,
}

impl<I, O, E, P> Parser<I, O, E> for AllConsuming<P>
where
    P: Parser<I, O, E>,
    E: ParseError<I>,
    I: InputLength,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O, E> {
        let (tail, value) = self.parser.parse(input)?;

        if tail.input_len() > 0 {
            Err(NomErr::Error(E::from_error_kind(tail, NomErrorKind::Eof)))
        } else {
            Ok((tail, value))
        }
    }
}

/// Parser which returns an error if the subparser returned
/// [`Incomplete`][nom::Err::Incomplete].
#[derive(Debug, Clone, Copy)]
pub struct Complete<P> {
    parser: P,
}

impl<I, O, E, P> Parser<I, O, E> for Complete<P>
where
    P: Parser<I, O, E>,
    E: ParseError<I>,
    I: Clone,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O, E> {
        self.parser
            .parse(input.clone())
            .map_err(move |err| match err {
                NomErr::Incomplete(..) => {
                    NomErr::Error(E::from_error_kind(input, NomErrorKind::Complete))
                }
                err => err,
            })
    }
}

/// Parser which returns a [`Failure`][nom::Err::Failure] if the subparser
/// returned an error. This prevents other branches from being tried.
#[derive(Debug, Clone, Copy)]
pub struct Cut<P> {
    parser: P,
}

impl<I, O, E, P> Parser<I, O, E> for Cut<P>
where
    P: Parser<I, O, E>,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O, E> {
        self.parser.parse(input).map_err(|err| match err {
            NomErr::Error(err) => NomErr::Failure(err),
            err => err,
        })
    }
}

/// Parser which wraps the subparser output in an [`Option`], and returns a
/// successful [`None`] output if it fails.
#[derive(Debug, Clone, Copy)]
pub struct Optional<P> {
    parser: P,
}

impl<I, O, E, P> Parser<I, Option<O>, E> for Optional<P>
where
    P: Parser<I, O, E>,
    I: Clone,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, Option<O>, E> {
        match self.parser.parse(input.clone()) {
            Ok((tail, value)) => Ok((tail, Some(value))),
            Err(NomErr::Error(_)) => Ok((input, None)),
            Err(e) => Err(e),
        }
    }
}

/// Parser which, when successful, discards the output of the subparser and
/// instead returns the consumed input.
#[derive(Debug, Clone, Copy)]
pub struct Recognize<P, O> {
    parser: WithRecognized<P>,
    phantom: PhantomData<O>,
}

impl<I, O, E, P> Parser<I, I, E> for Recognize<P, O>
where
    P: Parser<I, O, E>,
    I: Clone + Slice<RangeTo<usize>> + Offset,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, I, E> {
        self.parser
            .parse(input)
            .map(|(tail, (recognized, _))| (tail, recognized))
    }
}

/// Parser which, when successful, returns the result of the inner parser and
/// also the consumed input
#[derive(Debug, Clone, Copy)]
pub struct WithRecognized<P> {
    parser: P,
}

impl<I, O, E, P> Parser<I, (I, O), E> for WithRecognized<P>
where
    P: Parser<I, O, E>,
    I: Clone + Slice<RangeTo<usize>> + Offset,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, (I, O), E> {
        let (tail, output) = self.parser.parse(input.clone())?;
        let index = input.offset(&tail);
        Ok((tail, (input.slice(..index), output)))
    }
}

/// Parser which, when successful, discards the output of the subparser and
/// instead returns a clone of a value.
#[derive(Debug, Clone, Copy)]
pub struct Value<T, P, O> {
    parser: P,
    value: T,
    phantom: PhantomData<O>,
}

impl<I, O, E, T, P> Parser<I, T, E> for Value<T, P, O>
where
    P: Parser<I, O, E>,
    T: Clone,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, T, E> {
        self.parser
            .parse(input)
            .map(|(input, _)| (input, self.value.clone()))
    }
}

/// Parser which checks the output of its subparser against a verifier function.
#[derive(Debug, Clone, Copy)]
pub struct Verify<P, F> {
    parser: P,
    verifier: F,
}

impl<I, O, E, P, F> Parser<I, O, E> for Verify<P, F>
where
    P: Parser<I, O, E>,
    E: ParseError<I>,
    F: Fn(&O) -> bool,
    I: Clone,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O, E> {
        let (tail, value) = self.parser.parse(input.clone())?;

        match (self.verifier)(&value) {
            true => Ok((tail, value)),
            false => Err(NomErr::Error(E::from_error_kind(
                input,
                NomErrorKind::Verify,
            ))),
        }
    }
}

/// Parser which attaches additional context to any errors returned by the
/// subparser.
#[derive(Debug, Clone, Copy)]
pub struct Context<P> {
    context: &'static str,
    parser: P,
}

impl<I, O, E, P> Parser<I, O, E> for Context<P>
where
    P: Parser<I, O, E>,
    E: ContextError<I>,
    I: Clone,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O, E> {
        self.parser
            .parse(input.clone())
            .map_err(move |err| err.map(move |err| E::add_context(input, self.context, err)))
    }
}

/// Parser which gets and discards an output from a second subparser,
/// returning the output from the original parser if both were successful.
#[derive(Debug, Clone, Copy)]
pub struct Terminated<P1, P2, O2> {
    parser: P1,
    terminator: P2,
    phantom: PhantomData<O2>,
}

impl<I, O1, O2, E, P1, P2> Parser<I, O1, E> for Terminated<P1, P2, O2>
where
    P1: Parser<I, O1, E>,
    P2: Parser<I, O2, E>,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O1, E> {
        let (input, value) = self.parser.parse(input)?;
        let (input, _) = self.terminator.parse(input)?;

        Ok((input, value))
    }
}

/// Parser which gets and discards an output from a prefix subparser before
/// running the main subparser. Returns the output from the main subparser if
/// both were successful.
#[derive(Debug, Clone, Copy)]
pub struct Preceded<P1, P2, O2> {
    parser: P1,
    prefix: P2,
    phantom: PhantomData<O2>,
}

impl<I, O1, O2, E, P1, P2> Parser<I, O1, E> for Preceded<P1, P2, O2>
where
    P1: Parser<I, O1, E>,
    P2: Parser<I, O2, E>,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O1, E> {
        let (input, _) = self.prefix.parse(input)?;
        self.parser.parse(input)
    }
}

/// Parser which gets and discards a delimiting value both before and after the
/// main subparser. Returns the output from the main subparser if all were
/// successful.
#[derive(Debug, Clone, Copy)]
pub struct Delimited<P, D, O2> {
    parser: P,
    delimiter: D,
    phantom: PhantomData<O2>,
}

impl<P, D, I, O, E, O2> Parser<I, O, E> for Delimited<P, D, O2>
where
    P: Parser<I, O, E>,
    D: Parser<I, O2, E>,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O, E> {
        let (input, _) = self.delimiter.parse(input)?;
        let (input, value) = self.parser.parse(input)?;
        let (input, _) = self.delimiter.parse(input)?;

        Ok((input, value))
    }
}

/// Parser which runs a fallible mapping function on the output of the
/// subparser. Any errors returned by the mapping function are transformed
/// into a parse error.
///
#[derive(Debug, Clone, Copy)]
pub struct MapRes<P, F, O, E2> {
    parser: P,
    func: F,
    phantom: PhantomData<(O, E2)>,
}

impl<P, F, I, O, E, O2, E2> Parser<I, O2, E> for MapRes<P, F, O, E2>
where
    P: Parser<I, O, E>,
    F: FnMut(O) -> Result<O2, E2>,
    E: FromExternalError<I, E2>,
    I: Clone,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O2, E> {
        let (tail, value) = self.parser.parse(input.clone())?;

        (self.func)(value)
            .map(move |value| (tail, value))
            .map_err(move |err| {
                NomErr::Error(E::from_external_error(input, NomErrorKind::MapRes, err))
            })
    }
}

/// Parser which runs a fallible mapping function on the output of the
/// subparser. Any errors returned by the mapping function are transformed
/// into a parse failure.
///
#[derive(Debug, Clone, Copy)]
pub struct MapResCut<P, F, O, E2> {
    parser: P,
    func: F,
    phantom: PhantomData<(O, E2)>,
}

impl<P, F, I, O, E, O2, E2> Parser<I, O2, E> for MapResCut<P, F, O, E2>
where
    P: Parser<I, O, E>,
    F: FnMut(O) -> Result<O2, E2>,
    E: FromExternalError<I, E2>,
    I: Clone,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O2, E> {
        let (tail, value) = self.parser.parse(input.clone())?;

        (self.func)(value)
            .map(move |value| (tail, value))
            .map_err(move |err| {
                NomErr::Failure(E::from_external_error(input, NomErrorKind::MapRes, err))
            })
    }
}
/// Parser which runs a subparser but doesn't consume any input
#[derive(Debug, Clone, Copy)]
pub struct Peek<P> {
    parser: P,
}

impl<I, O, E, P> Parser<I, O, E> for Peek<P>
where
    P: Parser<I, O, E>,
    I: Clone,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, O, E> {
        self.parser
            .parse(input.clone())
            .map(|(_, value)| (input, value))
    }
}

/// Parser which returns failure if the subparser succeeds, and succeeds if the
/// subparser fails.
#[derive(Debug, Clone, Copy)]
pub struct Not<P, O> {
    parser: P,
    phantom: PhantomData<O>,
}

impl<I, O, E, P> Parser<I, (), E> for Not<P, O>
where
    P: Parser<I, O, E>,
    I: Clone,
    E: ParseError<I>,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, (), E> {
        match self.parser.parse(input.clone()) {
            Ok(..) => Err(NomErr::Error(E::from_error_kind(input, NomErrorKind::Not))),
            Err(NomErr::Error(..)) => Ok((input, ())),
            Err(err) => Err(err),
        }
    }
}

/// Parser which parses something via [`FromStr`], using a subparser as a
/// recognizer for the string to pass to [`from_str`][FromStr::from_str].
#[derive(Debug, Clone, Copy)]
pub struct FromStrParser<P, T> {
    parser: P,
    phantom: PhantomData<T>,
}

impl<'a, T, E, P> Parser<&'a str, T, E> for FromStrParser<P, T>
where
    P: Parser<&'a str, &'a str, E>,
    T: FromStr,
    E: FromExternalError<&'a str, T::Err>,
{
    #[inline]
    fn parse(&mut self, input: &'a str) -> nom::IResult<&'a str, T, E> {
        let (tail, value_str) = self.parser.parse(input)?;
        match value_str.parse() {
            Ok(value) => Ok((tail, value)),
            Err(parse_err) => Err(NomErr::Error(E::from_external_error(
                input,
                NomErrorKind::MapRes,
                parse_err,
            ))),
        }
    }
}

/// Parser which parses something via [`FromStr`], using a subparser as a
/// recognizer for the string to pass to [`from_str`][FromStr::from_str].
/// Returns [`Err::Failure`][NomErr::Failure] if the [`FromStr`] parse fails.
#[derive(Debug, Clone, Copy)]
pub struct FromStrCutParser<P, T> {
    parser: P,
    phantom: PhantomData<T>,
}

impl<'a, T, E, P> Parser<&'a str, T, E> for FromStrCutParser<P, T>
where
    P: Parser<&'a str, &'a str, E>,
    T: FromStr,
    E: FromExternalError<&'a str, T::Err>,
{
    #[inline]
    fn parse(&mut self, input: &'a str) -> nom::IResult<&'a str, T, E> {
        let (tail, value_str) = self.parser.parse(input)?;
        match value_str.parse() {
            Ok(value) => Ok((tail, value)),
            Err(parse_err) => Err(NomErr::Failure(E::from_external_error(
                input,
                NomErrorKind::MapRes,
                parse_err,
            ))),
        }
    }
}

/// Parser which parses an array by running a subparser in a loop a fixed
/// number of times.
#[derive(Debug, Clone, Copy)]
pub struct ArrayParser<P> {
    parser: P,
}

impl<P, I, O, E, const N: usize> Parser<I, [O; N], E> for ArrayParser<P>
where
    P: Parser<I, O, E>,
{
    fn parse(&mut self, input: I) -> nom::IResult<I, [O; N], E> {
        // TODO: create a folding version of brownstone::try_build so that
        // this Some trick isn't necessary
        let mut input = Some(input);

        brownstone::try_build(|| {
            let (tail, value) = self.parser.parse(input.take().unwrap())?;
            input = Some(tail);
            Ok(value)
        })
        .map(|array| (input.unwrap(), array))
        .map_err(|err| err.error)
    }
}

/// Parser which parses an array by running a subparser in a loop a fixed
/// number of times, parsing a separator between each item.
#[derive(Debug, Clone, Copy)]
pub struct SeparatedArrayParser<P1, P2, O2> {
    parser: P1,
    separator: P2,
    phantom: PhantomData<O2>,
}

impl<I, O1, O2, E, P1, P2, const N: usize> Parser<I, [O1; N], E>
    for SeparatedArrayParser<P1, P2, O2>
where
    P1: Parser<I, O1, E>,
    P2: Parser<I, O2, E>,
{
    fn parse(&mut self, input: I) -> nom::IResult<I, [O1; N], E> {
        // TODO: create a folding version of brownstone::try_build so that
        // this Some trick isn't necessary
        let mut input = Some(input);

        brownstone::try_build_indexed(|idx| {
            let local_input = input.take().unwrap();

            let (tail, value) = match idx {
                0 => self.parser.parse(local_input),
                _ => self
                    .parser
                    .by_ref()
                    .preceded_by(self.separator.by_ref())
                    .parse(local_input),
            }?;

            input = Some(tail);
            Ok(value)
        })
        .map(|array| (input.unwrap(), array))
        .map_err(|err| err.error)
    }
}
