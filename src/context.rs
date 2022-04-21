use nom::error::{Error, ErrorKind, VerboseError, VerboseErrorKind};

/// Updated version of [`nom::error::ContextError`]. Allows for arbitrary
/// context types, rather than requiring `&'static str`
pub trait ContextError<I, C>: Sized {
    /// Create a new error from an input position, a context, and an existing
    /// error. This is used by the [`.context`][crate::ParserExt::context]
    /// combinator to add friendly information to errors when backtracking
    /// through a parse tree.
    fn add_context(location: I, ctx: C, other: Self) -> Self;
}

impl<I, C> ContextError<I, C> for () {
    fn add_context(_location: I, _ctx: C, _other: Self) -> Self {}
}

impl<I, C> ContextError<I, C> for (I, ErrorKind) {
    fn add_context(_location: I, _ctx: C, other: Self) -> Self {
        other
    }
}

impl<I, C> ContextError<I, C> for Error<I> {
    fn add_context(_location: I, _ctx: C, other: Self) -> Self {
        other
    }
}

impl<I> ContextError<I, &'static str> for VerboseError<I> {
    fn add_context(location: I, ctx: &'static str, mut other: Self) -> Self {
        other
            .errors
            .push((location, VerboseErrorKind::Context(ctx)));

        other
    }
}
