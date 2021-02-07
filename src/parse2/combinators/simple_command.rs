use crate::ast::{RedirectOrCmdWord, RedirectOrEnvVar, SimpleCommand};
use crate::error::ParseError;
use crate::iter::{Multipeek, PositionIterator};
use crate::parse2::combinators;
use crate::parse2::Parser;
use crate::token::Token;

/// Tries to parse a simple command, e.g. `cmd arg1 arg2 >redirect`.
///
/// A valid command is expected to have at least an executable name, or a single
/// variable assignment or redirection. Otherwise an error will be returned.
pub fn simple_command<I, W, R, PR, PW>(
    iter: &mut I,
    mut redirect: PR,
    mut word: PW,
) -> Result<SimpleCommand<String, W, R>, ParseError>
where
    I: ?Sized + Multipeek<Item = Token> + PositionIterator,
    PR: Parser<I, Output = Option<RedirectOrCmdWord<R, W>>, Error = ParseError>,
    PW: Parser<I, Output = Option<W>, Error = ParseError>,
{
    let mut vars = Vec::new();
    let mut cmd_args = Vec::new();

    loop {
        combinators::skip_whitespace(iter);
        let is_name = {
            let mut mp = iter.multipeek();
            if let Some(&Token::Name(_)) = mp.peek_next() {
                Some(&Token::Equals) == mp.peek_next()
            } else {
                false
            }
        };

        if is_name {
            let var = match iter.next() {
                Some(Token::Name(var)) => {
                    iter.next(); // Consume the =
                    var
                }
                _ => unreachable!(),
            };

            let mut mp = iter.multipeek();
            let value = if let Some(&Token::Whitespace(_)) = mp.peek_next() {
                None
            } else {
                drop(mp);
                word.parse(iter)?
            };
            vars.push(RedirectOrEnvVar::EnvVar(var, value));

            // Make sure we continue checking for assignments,
            // otherwise it they can be interpreted as literal words.
            continue;
        }

        // If we find a redirect we should keep checking for
        // more redirects or assignments. Otherwise we will either
        // run into the command name or the end of the simple command.
        let exec = match redirect.parse(iter)? {
            Some(RedirectOrCmdWord::Redirect(redirect)) => {
                vars.push(RedirectOrEnvVar::Redirect(redirect));
                continue;
            }
            Some(RedirectOrCmdWord::CmdWord(w)) => w,
            None => break,
        };

        // Since there are no more assignments or redirects present
        // it must be the first real word, and thus the executable name.
        cmd_args.push(RedirectOrCmdWord::CmdWord(exec));
        break;
    }

    let vars = vars;

    // Now that all assignments are taken care of, any other occurances of `=` will be
    // treated as literals when we attempt to parse a word out.
    while let Some(arg) = redirect.parse(iter)? {
        cmd_args.push(arg);
    }

    // "Blank" commands are only allowed if redirection occurs
    // or if there is some variable assignment
    if vars.is_empty() && cmd_args.is_empty() {
        Err(combinators::make_unexpected_err(iter))
    } else {
        Ok(SimpleCommand {
            redirects_or_env_vars: vars,
            redirects_or_cmd_words: cmd_args,
        })
    }
}
