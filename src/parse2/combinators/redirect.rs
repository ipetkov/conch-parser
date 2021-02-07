use crate::ast::{Redirect, RedirectOrCmdWord};
use crate::error::ParseError;
use crate::iter::{Multipeek, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
use crate::token::Token;

/// Parses a continuous list of redirections and will error if any words
/// that are not valid file descriptors are found. Essentially used for
/// parsing redirection lists after a compound command like `while` or `if`.
pub fn redirect_list<I, W, R, P>(iter: &mut I, mut redirect: P) -> Result<Vec<R>, P::Error>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    P: Parser<I, Output = Option<RedirectOrCmdWord<R, W>>>,
    P::Error: From<ParseError>,
{
    let mut list = Vec::new();
    loop {
        combinators::skip_whitespace(iter);
        let start = iter.pos();
        match redirect.parse(iter)? {
            Some(RedirectOrCmdWord::Redirect(r)) => list.push(r),
            Some(RedirectOrCmdWord::CmdWord(_)) => {
                let err = ParseError::BadFd {
                    start,
                    end: iter.pos(),
                };
                return Err(err.into());
            }
            None => break,
        }
    }

    Ok(list)
}

/// Parses a redirection token an any source file descriptor and
/// path/destination descriptor as appropriate, e.g. `>out`, `1>& 2`, or `2>&-`.
///
/// Since the source descriptor can be any arbitrarily complicated word,
/// it makes it difficult to reliably peek forward whether a valid redirection
/// exists without consuming anything. Thus this method may return a simple word
/// if no redirection is found.
///
/// Thus, unless a parse error is occured, the return value will be an optional
/// redirect or word if either is found. In other words, `Ok(Some(Ok(redirect)))`
/// will result if a redirect is found, `Ok(Some(Err(word)))` if a word is found,
/// or `Ok(None)` if neither is found.
pub fn redirect<I, W, PW, PH>(
    iter: &mut I,
    word_as_num: impl Fn(&W) -> Option<u16>,
    is_word_numeric: impl Fn(&W) -> bool,
    make_word_from_str: impl FnOnce(&str) -> W,
    mut word: PW,
    mut heredoc: PH,
) -> Result<Option<RedirectOrCmdWord<Redirect<W>, W>>, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    PW: Parser<I, Output = Option<W>, Error = ParseError>,
    PH: Parser<I, Output = W, Error = ParseError>,
{
    let (src_fd, src_fd_as_word) = match word.parse(iter)? {
        None => (None, None),
        Some(w) => match word_as_num(&w) {
            Some(num) => (Some(num), Some(w)),
            None => return Ok(Some(RedirectOrCmdWord::CmdWord(w))),
        },
    };

    // NB: don't skip whitespace here, as whitespace would preclude
    // a word from being a potential fd candidate

    let mut mp = iter.multipeek();
    let is_heredoc = matches!(mp.peek_next(), Some(Token::DLess) | Some(Token::DLessDash));
    drop(mp);
    if is_heredoc {
        let heredoc = Redirect::Heredoc(src_fd, heredoc.parse(iter)?);
        return Ok(Some(RedirectOrCmdWord::Redirect(heredoc)));
    }

    let is_dup;
    let constructor = eat_maybe!(iter, {
        Token::Less      => {
            is_dup = false;
            Redirect::Read
        },
        Token::Great     => {
            is_dup = false;
            Redirect::Write
        },
        Token::DGreat    => {
            is_dup = false;
            Redirect::Append
        },
        Token::Clobber   => {
            is_dup = false;
            Redirect::Clobber
        },
        Token::LessGreat => {
            is_dup = false;
            Redirect::ReadWrite
        },

        Token::LessAnd   => {
            is_dup = true;
            Redirect::DupRead
        },
        Token::GreatAnd  => {
            is_dup = true;
            Redirect::DupWrite
        };

        _ => return Ok(src_fd_as_word.map(RedirectOrCmdWord::CmdWord)),

    });

    let path = if is_dup {
        combinators::skip_whitespace(iter);

        if let Some(_) = combinators::peek_reserved_token(iter, &[Token::Dash]) {
            iter.next(); // Consume the Dash
            make_word_from_str(Token::Dash.as_str())
        } else {
            let path_start_pos = iter.pos();
            let path = match word.parse(iter)? {
                Some(p) => p,
                None => return Err(combinators::make_unexpected_err(iter)),
            };

            if !is_word_numeric(&path) {
                return Err(ParseError::BadFd {
                    start: path_start_pos,
                    end: iter.pos(),
                });
            }
            path
        }
    } else {
        match word.parse(iter)? {
            Some(p) => p,
            None => return Err(combinators::make_unexpected_err(iter)),
        }
    };

    Ok(Some(RedirectOrCmdWord::Redirect(constructor(src_fd, path))))
}
