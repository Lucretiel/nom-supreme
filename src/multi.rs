//! Additional parser combinators for running subparsers in a loop. Generally
//! designed to try to provide more useful errors by being aware of a terminal
//! condition.

use std::convert::Infallible;

use nom::{
    error::{append_error, ErrorKind, FromExternalError, ParseError},
    Err::{Error, Failure, Incomplete},
    Parser,
};
use ErrorKind::Many1;

fn make_infallible<A, B>(
    mut func: impl FnMut(A, B) -> A,
) -> impl FnMut(A, B) -> Result<A, Infallible> {
    move |a, b| Ok(func(a, b))
}

/// The perfected folding parser. Parses a series of 1 more more things,
/// separated by some `separator`, terminated by some `terminator`, folding
/// all of them together.
///
/// When parsing begins, an accumulator value is created with init(). Then,
/// each parsed item will be folded into the accumulator via the `fold`
/// function. After parsing each item, `parse_separated_terminated` will
/// attempt to parse a `terminator`. If it succeeds, it will return the
/// accumulator; otherwise, it will attempt to parse a separator. If it fails
/// to parse either a separator or a terminator, it will return an error;
/// otherwise, it will continue on to parse and fold the next item.
///
/// If you want 0 or more things to be parsed, wrap this in
/// [`opt`][crate::parser_ext::ParserExt::opt] or [`alt`][nom::branch::alt].
///
/// This parser will stop as soon as it finds a `terminator`. If you wish to
/// have a `terminator` parser that is the same as your `separator`, you'll
/// need to add some extra context to the terminator parser; perhaps a
/// lookahead with [`peek`][crate::ParserExt::peek].
///
/// This parser exists to provide meaningful parse errors. By requiring a
/// terminator, we can ensure that it doesn't suffer from the normal folding
/// parser problem of unconditionally returning success because all parse
/// failures simply end the fold without knowing if there's a larger problem.
///
/// `parse_separated_terminated` will attempt to smartly allow 0-length
/// matches. It will allow subparsers to have 0-length matches, but if a full
/// loop is made without any progress being made, it will return an error.
#[inline]
pub fn parse_separated_terminated<Input, ParseOutput, SepOutput, TermOutput, ParseErr, Accum>(
    parser: impl Parser<Input, ParseOutput, ParseErr>,
    separator: impl Parser<Input, SepOutput, ParseErr>,
    terminator: impl Parser<Input, TermOutput, ParseErr>,

    init: impl FnMut() -> Accum,
    fold: impl FnMut(Accum, ParseOutput) -> Accum,
) -> impl Parser<Input, Accum, ParseErr>
where
    Input: Clone,
    ParseErr: ParseError<Input>,
{
    parse_separated_terminated_impl(
        parser,
        separator,
        terminator,
        init,
        make_infallible(fold),
        |_input, _err| unreachable!(),
    )
}

/// The perfected folding parser. Parses a series of 1 more more things,
/// separated by some `separator`, terminated by some `terminator`, folding
/// all of them together with a fallible fold function.
///
/// This function is identical to [`parse_separated_terminated`], except that
/// the fold function may return an error. See its documentation for more
/// details about the precise behavior of this parser.
#[inline]
pub fn parse_separated_terminated_res<
    Input,
    ParseOutput,
    SepOutput,
    TermOutput,
    ParseErr,
    Accum,
    FoldErr,
>(
    parser: impl Parser<Input, ParseOutput, ParseErr>,
    separator: impl Parser<Input, SepOutput, ParseErr>,
    terminator: impl Parser<Input, TermOutput, ParseErr>,

    init: impl FnMut() -> Accum,
    fold: impl FnMut(Accum, ParseOutput) -> Result<Accum, FoldErr>,
) -> impl Parser<Input, Accum, ParseErr>
where
    Input: Clone,
    ParseErr: ParseError<Input> + FromExternalError<Input, FoldErr>,
{
    parse_separated_terminated_impl(parser, separator, terminator, init, fold, |input, err| {
        ParseErr::from_external_error(input, Many1, err)
    })
}

/// Shared implementation for parse_separated_terminated_res and
/// parse_separated_terminated. This exists so that we don't have to have an
/// unnecessary bound of FromExternalError on parse_separated_terminated.
#[inline]
fn parse_separated_terminated_impl<
    Input,
    ParseOutput,
    SepOutput,
    TermOutput,
    ParseErr,
    Accum,
    FoldErr,
>(
    mut parser: impl Parser<Input, ParseOutput, ParseErr>,
    mut separator: impl Parser<Input, SepOutput, ParseErr>,
    mut terminator: impl Parser<Input, TermOutput, ParseErr>,

    mut init: impl FnMut() -> Accum,
    mut fold: impl FnMut(Accum, ParseOutput) -> Result<Accum, FoldErr>,

    mut build_error: impl FnMut(Input, FoldErr) -> ParseErr,
) -> impl Parser<Input, Accum, ParseErr>
where
    Input: Clone,
    ParseErr: ParseError<Input>,
{
    move |mut input: Input| {
        let mut accum = init();

        // TODO: various kinds of 0-length tracking:
        // - If we go a full loop without making any progress, that's an error
        // - If the separator matches a 0-length match, and the parser fails,
        //   include the most recent terminator error along with the parser
        //   parser error. It *might* be worth doing this even if separator
        //   is non-zero length? For example, suppose the separator is , and
        //   the terminator is , with a peeking lookahead. It might be worth
        //   knowing that the terminator was tried and failed there.
        loop {
            // Try to find a value. To fail to do so at this point is an
            // error, since we either just started or successfully parsed a
            // separator.
            let (tail, value) = match parser.parse(input.clone()) {
                Ok(success) => success,
                Err(err) => break Err(err.map(move |err| append_error(input, Many1, err))),
            };

            accum = fold(accum, value).map_err(|err| Error(build_error(input, err)))?;
            input = tail;

            // Try to find a terminator; if we found it, we're done.
            let term_err = match terminator.parse(input.clone()) {
                // We found a terminator, so we're done
                Ok((tail, _)) => break Ok((tail, accum)),

                // No terminator. Keep track of the error in case we also fail
                // to find a separator.
                Err(Error(err)) => err,

                // Other kinds of errors should be returned immediately.
                Err(Failure(err)) => break Err(Failure(ParseErr::append(input, Many1, err))),
                Err(Incomplete(n)) => break Err(Incomplete(n)),
            };

            // No terminator, so instead try to find a separator
            let tail = match separator.parse(input.clone()) {
                Ok((tail, _)) => tail,
                Err(Incomplete(n)) => break Err(Incomplete(n)),
                Err(Error(err)) => {
                    break Err(Error(append_error(
                        input,
                        Many1,
                        ParseErr::or(err, term_err),
                    )))
                }
                Err(Failure(err)) => break (Err(Failure(append_error(input, Many1, err)))),
            };

            input = tail;
        }
    }
}
