//! Entry point layer into nom parsers. See [`final_parser`] for details.

use std::fmt::{self, Display, Formatter};

use nom::{
    error::{Error, ErrorKind, ParseError, VerboseError},
    Err as NomErr, InputLength, Offset, Parser,
};

use crate::parser_ext::ParserExt;

/// Trait for types which represent an absolute location of a parse error in
/// an input
///
/// This trait is implemented for "full location context" types; that is, for
/// types that capture the exact location (and possibly other related context)
/// of a parse error for the purpose of reporting. Two such types are provided
/// by `nom-supreme`: [`Location`], which captures the line and column number
/// of the error, and [`ByteOffset`], which captures the byte offset of the
/// error.
///
/// This trait is usually paired with [`ExtractContext`], a trait used by
/// nom error types to convert the stored input tail types into location
/// contexts. [`ExtractContext`] is in turn used by [`final_parser`] to create
/// & return parse errors with the full attached context.
pub trait RecreateContext<I>: Sized {
    /// Given the *original* input, as well as the context reported by nom,
    /// recreate a context in the original string where the error occurred.
    ///
    /// This function may return garbage or panic if the tail is not associated
    /// with the original input.
    fn recreate_context(original_input: I, tail: I) -> Self;
}

impl<I> RecreateContext<I> for I {
    fn recreate_context(_original_input: I, tail: I) -> Self {
        tail
    }
}

/// A byte offset into the input where an error may have occurred
///
/// # `&str` Example
///
/// ```
/// use nom_supreme::final_parser::{ByteOffset, RecreateContext};
///
/// let original_input = "Hello,\nWorld!\n";
/// let tail = &original_input[9..];
///
/// assert_eq!(
///    ByteOffset::recreate_context(original_input, tail),
///    ByteOffset(9),
/// );
/// ```
///
/// `# &[u8]` Example
///
/// ```
/// use nom_supreme::final_parser::{ByteOffset, RecreateContext};
///
/// let original_input = b"GET / HTTP/1.1\r\n";
/// let tail = &original_input[6..];
///
/// assert_eq!(
///    ByteOffset::recreate_context(&original_input[..], tail),
///    ByteOffset(6),
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ByteOffset(pub usize);

impl<I: Offset> RecreateContext<I> for ByteOffset {
    fn recreate_context(original_input: I, tail: I) -> Self {
        ByteOffset(original_input.offset(&tail))
    }
}

/// A location in a string where an error may have occurred. In keeping with
/// the typical practice from editors and other tools, line and columns are both
/// 1-indexed.
///
/// # Example
///
/// ```
/// use nom_supreme::final_parser::{RecreateContext, Location};
///
/// let original_input = "Hello,\nWorld!\n";
/// let tail = &original_input[9..];
///
/// assert_eq!(
///    Location::recreate_context(original_input, tail),
///    Location { line: 2, column: 3 },
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Location {
    /// The line number in the original input where the error occurred
    pub line: usize,

    /// The column of the line in the original input where the error occurred
    pub column: usize,
}

impl Location {
    /// Given the *original* input string, as well as the context reported by
    /// nom, compute the location in the original string where the error
    /// occurred.
    ///
    /// This function will report garbage (and may panic) if the context is not
    /// associated with the input
    pub fn locate_tail<'a>(original_input: &'a str, tail: &'a str) -> Self {
        let offset = original_input.offset(tail);
        let input_bytes = original_input.as_bytes();
        let prefix = &input_bytes[..offset];

        let line_number = memchr::memchr_iter(b'\n', prefix).count() + 1;

        let last_line_start = memchr::memrchr(b'\n', prefix).map(|i| i + 1).unwrap_or(0);
        let last_line = &prefix[last_line_start..];
        let column_number = last_line.len() + 1;

        Location {
            line: line_number,
            column: column_number,
        }
    }
}

impl Display for Location {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        if f.alternate() {
            write!(f, "line {}, column {}", self.line, self.column)
        } else {
            write!(f, "{}:{}", self.line, self.column)
        }
    }
}

impl RecreateContext<&str> for Location {
    fn recreate_context(original_input: &str, tail: &str) -> Self {
        Location::locate_tail(original_input, tail)
    }
}

/// Trait for recombining error information with the original input.
///
/// This trait is used to take the context information attached to nom errors-
/// specifically, the tail of the input indicating the location of the input-
/// and recombine it with the *original* input to produce an error with
/// something more useful for error reporting.
///
/// Typically, it looks like  `ExtractContext<I, E<T>> for E<I>`. This
/// indicates that some error type `E`, which is generic over the input type,
/// can be converted into another variant of that error, using `T` instead of
/// `I` to hold the result context. Often this context conversion can happen
/// with [`RecreateContext`].
pub trait ExtractContext<I, T> {
    /// Given the context attached to a nom error, and given the *original*
    /// input to the nom parser, extract more the useful context information.
    ///
    /// For example, for a string, 1 possible context extraction would be the
    /// Location (line and column number) in the original input where the error
    /// indicated by self occurred.
    fn extract_context(self, original_input: I) -> T;
}

impl<I, T> ExtractContext<I, ()> for T {
    fn extract_context(self, _original_input: I) {}
}

impl<I, T> ExtractContext<I, (T, ErrorKind)> for (I, ErrorKind)
where
    T: RecreateContext<I>,
{
    fn extract_context(self, original_input: I) -> (T, ErrorKind) {
        let (tail, kind) = self;
        (T::recreate_context(original_input, tail), kind)
    }
}

impl<I, T> ExtractContext<I, Error<T>> for Error<I>
where
    T: RecreateContext<I>,
{
    fn extract_context(self, original_input: I) -> Error<T> {
        Error::new(T::recreate_context(original_input, self.input), self.code)
    }
}

impl<I, T> ExtractContext<I, VerboseError<T>> for VerboseError<I>
where
    T: RecreateContext<I>,
    I: Clone,
{
    fn extract_context(self, original_input: I) -> VerboseError<T> {
        VerboseError {
            errors: self
                .errors
                .into_iter()
                .map(|(input, kind)| (T::recreate_context(original_input.clone(), input), kind))
                .collect(),
        }
    }
}

/// `extract_context` can be used directly on `Result` values that have an
/// error with `ExtractContext`
impl<T, E1, E2, I> ExtractContext<I, Result<T, E2>> for Result<T, E1>
where
    E1: ExtractContext<I, E2>,
{
    fn extract_context(self, original_input: I) -> Result<T, E2> {
        self.map_err(move |err| err.extract_context(original_input))
    }
}

/// Bootstrapping layer for a nom parser.
///
/// This function is intended to be the entry point into a nom parser; it
/// represents in some sense the "end of composability". It creates a function
/// which applies a parser to an input. The parser is configured such that it
/// must parse the *entire* input, and any "Incomplete" responses are reported
/// as errors. Additionally, if the parser returns an error, the context
/// information in the error is recombined with the original input via
/// `ExtractContext` to create a more useful error.
pub fn final_parser<I, O, E, E2>(parser: impl Parser<I, O, E>) -> impl FnMut(I) -> Result<O, E2>
where
    E: ParseError<I> + ExtractContext<I, E2>,
    I: InputLength + Clone,
{
    let mut parser = parser.complete().all_consuming();

    move |input| match parser.parse(input.clone()) {
        Ok((_, parsed)) => Ok(parsed),
        Err(NomErr::Error(err)) | Err(NomErr::Failure(err)) => Err(err.extract_context(input)),
        Err(NomErr::Incomplete(..)) => {
            unreachable!("Complete combinator should make this impossible")
        }
    }
}
