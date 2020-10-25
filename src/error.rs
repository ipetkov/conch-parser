//! Errors which may arise during parsing.

use crate::parse::SourcePos;
use crate::token::Token;
use std::error::Error;
use std::fmt;

/// The error type which is returned from parsing shell commands.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParseError {
    /// Encountered a word that could not be interpreted as a valid file descriptor.
    /// Stores the start and end position of the invalid word.
    BadFd {
        /// Starting position of the invalid word.
        start: SourcePos,
        /// Ending position of the invalid word.
        end: SourcePos,
    },
    /// Encountered a `Token::Literal` where expecting a `Token::Name`.
    BadIdent(String, SourcePos),
    /// Encountered a bad token inside of `${...}`.
    BadSubst(Token, SourcePos),
    /// Encountered EOF while looking for a match for the specified token.
    /// Stores position of opening token.
    Unmatched(UnmatchedError),
    /// Did not find a reserved keyword within a command. The first String is the
    /// command being parsed, followed by the position of where it starts. Next
    /// is the missing keyword followed by the position of where the parse
    /// expected to have encountered it.
    IncompleteCmd {
        /// The command being parsed.
        cmd: &'static str,
        /// The starting position of the command.
        cmd_pos: SourcePos,
        /// The keyword which we failed to find as expected.
        kw: &'static str,
        /// The position of where the missing keyword was expected.
        kw_pos: SourcePos,
    },
    /// Encountered a token not appropriate for the current context.
    Unexpected(Token, SourcePos),
    /// Encountered the end of input while expecting additional tokens.
    UnexpectedEOF,
}

impl Error for ParseError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            ParseError::Unmatched(e) => Some(e),

            ParseError::BadFd { .. }
            | ParseError::BadIdent(..)
            | ParseError::BadSubst(..)
            | ParseError::IncompleteCmd { .. }
            | ParseError::Unexpected(..)
            | ParseError::UnexpectedEOF => None,
        }
    }
}

impl From<UnmatchedError> for ParseError {
    fn from(e: UnmatchedError) -> Self {
        Self::Unmatched(e)
    }
}

impl fmt::Display for ParseError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ParseError::BadFd { start, end } => write!(
                fmt,
                "file descriptor found between lines {} - {} cannot possibly be a valid",
                start, end
            ),
            ParseError::BadIdent(id, pos) => write!(fmt, "not a valid identifier {}: {}", pos, id),
            ParseError::BadSubst(t, pos) => {
                write!(fmt, "bad substitution {}: invalid token: {}", pos, t)
            }
            ParseError::Unmatched(e) => e.fmt(fmt),

            ParseError::IncompleteCmd {
                cmd,
                cmd_pos,
                kw,
                kw_pos,
            } => write!(
                fmt,
                "did not find `{}` keyword on line {}, in `{}` command which starts on line {}",
                kw, kw_pos, cmd, cmd_pos
            ),

            // When printing unexpected newlines, print \n instead to avoid confusingly formatted messages
            ParseError::Unexpected(Token::Newline, pos) => {
                write!(fmt, "found unexpected token on line {}: \\n", pos)
            }
            ParseError::Unexpected(t, pos) => {
                write!(fmt, "found unexpected token on line {}: {}", pos, t)
            }

            ParseError::UnexpectedEOF => fmt.write_str("unexpected end of input"),
        }
    }
}

/// Indicates an error such that EOF was encountered while some unmatched
/// tokens were still pending. The error stores the unmatched token
/// and the position where it appears in the source.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UnmatchedError {
    /// The token opening token we were expecting to match.
    pub token: Token,
    /// The position of `token`.
    pub pos: SourcePos,
}

impl Error for UnmatchedError {}

impl fmt::Display for UnmatchedError {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            fmt,
            "unmatched `{}` starting on line {}",
            self.token, self.pos
        )
    }
}

#[test]
fn ensure_errors_are_send_and_sync() {
    fn send_and_sync<T: Send + Sync>() {}

    send_and_sync::<ParseError>();
    send_and_sync::<UnmatchedError>();
}
