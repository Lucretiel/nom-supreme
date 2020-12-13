//! Adapter structs for building streaming parsers from sources of streaming
//! data, such as [`io::Read`][std::io::Read].

use std::io::{self, Read};

use nom::Parser;
use thiserror::Error;

/// Adapt an io::Read with a parser to read things off of the stream.
pub struct ByteStreamParser<R, P> {
    reader: Option<R>,
    parser: P,
    buffer: Vec<u8>,
    head: usize,
    tail: usize,
}

#[derive(Debug, Error)]
enum StreamingParseError<E> {
    #[error("i/o error while reading data to parse")]
    Io(#[from] io::Error),

    #[error("a parse error occurred")]
    Parse(#[source] E),

    #[error("a parser requested more data, but the buffer was full")]
    Overflow,

    #[error("a parser requested more data, but there's no more data in the reader")]
    Incomplete,

    #[error("there is no unparsed data and the reader is empty")]
    Done,
}

impl<R, P> ByteStreamParser<R, P> {
    fn buf(&self) -> &[u8] {
        &self.buffer[self.head..self.tail]
    }

    /// Move the contents of buffer to the front of the buffer, to prepare for
    /// another read
    fn shift_back(&mut self) {
        let size = self.tail - self.head;
        self.buffer.copy_within(self.head..self.tail, 0);
        self.head = 0;
        self.tail = size;
        
    }

    /// Fill the buffer. Loop read calls until the buffer is full or the reader
    /// is empty.
    fn fill_buffer(&mut self) -> io::Error<()> {
        match self
    }
}

impl<R: io::Read, P> ByteStreamParser<R, P> {
    fn parse_next<'a, T, E>(&'a mut self) -> Result<T, StreamingParseError<E>>
    where
        P: Parser<&'a [u8], T, E>,
    {
        // Prefill 
        if self.buf().is_empty() {
            match self.reader {
                None => return Err(StreamingParseError::Done),
                Some(ref mut R) => {
                    self.head = 0;
                    self.tail = 0;
                }
            }
        }
    }
}
