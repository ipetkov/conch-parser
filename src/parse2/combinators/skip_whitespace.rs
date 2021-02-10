use crate::iter::MultipeekIterator;
use crate::token::Token;

/// Skips over any encountered whitespace and escaped newlines,
/// but preserves regular newlines.
pub fn skip_whitespace<I>(iter: &mut I)
where
    I: ?Sized + MultipeekIterator<Item = Token>,
{
    loop {
        let mut mp = iter.multipeek();

        match mp.peek_next() {
            Some(Token::Whitespace(_)) => {
                drop(mp);
                iter.next();
                continue;
            }
            Some(Token::Backslash) => {
                if let Some(Token::Newline) = mp.peek_next() {
                    drop(mp);
                    iter.next();
                    iter.next();
                    continue;
                } else {
                    break;
                }
            }
            _ => break,
        }
    }
}

#[cfg(test)]
mod test {
    use crate::parse::iter::TokenIter;
    use crate::token::Token;

    fn test(mut to_skip: Vec<Token>, remaining: &[Token]) {
        to_skip.extend_from_slice(remaining);

        let mut iter = TokenIter::new(to_skip);
        super::skip_whitespace(&mut iter);

        assert_eq!(remaining, iter.collect::<Vec<_>>());
    }

    #[test]
    fn preserve_newline() {
        test(
            vec![
                Token::Whitespace("   ".into()),
                Token::Whitespace("\t\t".into()),
                Token::Whitespace(" ".into()),
                Token::Whitespace("\t".into()),
            ],
            &[Token::Newline, Token::Whitespace("   ".into())],
        );
    }

    #[test]
    fn preserve_comments() {
        test(
            vec![Token::Whitespace("  \t \t ".into())],
            &[
                Token::Pound,
                Token::Literal("comment".into()),
                Token::Newline,
                Token::Whitespace("   ".into()),
            ],
        );
    }

    #[test]
    fn skips_escaped_newlines() {
        test(
            vec![
                Token::Whitespace("  \t \t ".into()),
                Token::Backslash,
                Token::Newline,
                Token::Backslash,
                Token::Newline,
                Token::Whitespace(" ".into()),
                Token::Backslash,
                Token::Newline,
            ],
            &[Token::Newline, Token::Whitespace("   ".into())],
        );
    }
}
