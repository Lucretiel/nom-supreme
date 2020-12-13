//! Extensions to the nom [`Parser`][nom::Parser] trait which add postfix
//! versions of the common combinators. See [`ParserExt`] for details.

use std::{marker::PhantomData, ops::RangeTo};

use nom::{
    error::{ContextError, ErrorKind as NomErrorKind, FromExternalError, ParseError},
    Err as NomErr, InputLength, Offset, Parser, Slice,
};

/// Additional prefix parser combinators, as a complement to [`Parser`].
///
/// Compatibility note: it is expected that eventually many of these postfix
/// methods will eventually be added directly to the `Parser` trait. It will
/// therefore *not* be considered a compatibility break to remove those methods
/// from `ParserExt`, *if* they have the same name and signature.
pub trait ParserExt<I, O, E>: Parser<I, O, E> + Sized {
    /// Create a parser that must consume all of the input, or else return an
    /// error.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn all_consuming(self) -> AllConsuming<Self>
    where
        I: InputLength,
        E: ParseError<I>,
    {
        AllConsuming { parser: self }
    }

    /// Create a parser that transforms `Incomplete` into `Error`.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn complete(self) -> Complete<Self>
    where
        I: Clone,
        E: ParseError<I>,
    {
        Complete { parser: self }
    }

    /// Create a parser that transforms `Error` into `Failure`. This will
    /// end the parse immediately, even if there are other branches that
    /// could occur.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn cut(self) -> Cut<Self> {
        Cut { parser: self }
    }

    /// Create a parser that applies a mapping function `func` to the output
    /// of the subparser. Any errors from `func` will be transformed into
    /// parse errors.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn map_res<F, O2, E2>(self, func: F) -> MapRes<Self, F, O, E2>
    where
        F: FnMut(O) -> Result<O2, E2>,
        E: FromExternalError<I, E2>,
        I: Clone,
    {
        MapRes {
            parser: self,
            func,
            phantom: PhantomData,
        }
    }

    /// Make this parser optional; if it fails to parse, instead it returns
    /// None with the input in the original position.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn opt(self) -> Optional<Self>
    where
        I: Clone,
    {
        Optional { parser: self }
    }

    /// Replace this parser's output with the entire input that was consumed
    /// by the parser.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn recognize(self) -> Recognize<Self, O>
    where
        I: Clone + Slice<RangeTo<usize>> + Offset,
    {
        Recognize {
            parser: self,
            phantom: PhantomData,
        }
    }

    /// Replace this parser's output with a clone of `value` every time it
    /// finishes successfully.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn value<T: Clone>(self, value: T) -> Value<T, Self, O> {
        Value {
            parser: self,
            value,
            phantom: PhantomData,
        }
    }

    /// Require the output of this parser to pass a verifier function, or
    /// else return a parse error.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn verify<F>(self, verifier: F) -> Verify<Self, F>
    where
        F: Fn(&O) -> bool,
        I: Clone,
        E: ParseError<I>,
    {
        Verify {
            parser: self,
            verifier,
        }
    }

    /// Add some context to the parser. This context will be added to any
    /// errors that are returned from the parser.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn context(self, context: &'static str) -> Context<Self>
    where
        E: ContextError<I>,
        I: Clone,
    {
        Context {
            context,
            parser: self,
        }
    }

    /// Add a terminator parser. The terminator will run after this parser,
    /// returning any errors, but its output will otherwise be discarded.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn terminated<F, O2>(self, terminator: F) -> Terminated<Self, F, O2>
    where
        F: Parser<I, O2, E>,
    {
        Terminated {
            parser: self,
            terminator,
            phantom: PhantomData,
        }
    }

    /// Make this parser precede another one. The successor parser will run
    /// after this one succeeds, and the successor's output will be returned.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn precedes<F, O2>(self, successor: F) -> Preceded<F, Self, O>
    where
        F: Parser<I, O2, E>,
    {
        successor.preceded_by(self)
    }

    /// Make this parser preceded by another one. The prefix will run first,
    /// and if it succeeds, its output will be discard and this parser will
    /// be run.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn preceded_by<F, O2>(self, prefix: F) -> Preceded<Self, F, O2>
    where
        F: Parser<I, O2, E>,
    {
        Preceded {
            parser: self,
            prefix,
            phantom: PhantomData,
        }
    }

    /// Make this parser delimited, requiring both a prefix and a suffix.
    /// The output of the prefix and suffix is discarded.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn delimited_by<L, R, O1, O2>(
        self,
        prefix: L,
        suffix: R,
    ) -> Preceded<Terminated<Self, R, O2>, L, O1>
    where
        L: Parser<I, O1, E>,
        R: Parser<I, O2, E>,
    {
        self.terminated(suffix).preceded_by(prefix)
    }

    /// Same as delimited_by, but use the same parser for both sides.
    #[inline]
    #[must_use = "Parsers do nothing unless used"]
    fn delimited_by_both<F, O1>(self, delimiter: F) -> Preceded<Terminated<Self, F, O1>, F, O1>
    where
        F: Parser<I, O1, E> + Clone,
    {
        self.delimited_by(delimiter.clone(), delimiter)
    }
}

impl<I, O, E, P> ParserExt<I, O, E> for P where P: Parser<I, O, E> {}

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
    parser: P,
    phantom: PhantomData<O>,
}

impl<I, O, E, P> Parser<I, I, E> for Recognize<P, O>
where
    P: Parser<I, O, E>,
    I: Clone + Slice<RangeTo<usize>> + Offset,
{
    #[inline]
    fn parse(&mut self, input: I) -> nom::IResult<I, I, E> {
        let (tail, _) = self.parser.parse(input.clone())?;
        let index = input.offset(&tail);
        Ok((tail, input.slice(..index)))
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
        let (input, _) = self.parser.parse(input)?;
        Ok((input, self.value.clone()))
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

/// Parser which runs a fallible mapping function on the output of the
/// subparser. Any errors returned by the mapping function are transformed
/// into a parse error.
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
