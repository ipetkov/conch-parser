use crate::ast::builder;
use crate::iter::Multipeek;
use crate::parse::combinators;
use crate::token::Token;

/// Parses zero or more `Token::Newline`s, skipping leading whitespace and capturing comments.
pub fn linebreak<I>(iter: &mut I) -> Vec<builder::Newline>
where
    I: ?Sized + Multipeek<Item = Token>,
{
    let mut lines = Vec::new();
    while let Some(n) = newline(iter) {
        lines.push(n);
    }
    lines
}

/// Tries to parse a `Token::Newline` (or a comment) after skipping leading whitespace.
pub fn newline<I>(iter: &mut I) -> Option<builder::Newline>
where
    I: ?Sized + Multipeek<Item = Token>,
{
    combinators::skip_whitespace(iter);

    let mut mp = iter.multipeek();
    match mp.peek_next() {
        Some(Token::Pound) => {
            drop(mp);

            let mut comment = String::new();
            for t in iter.take_while(|t| *t != Token::Newline) {
                comment.push_str(t.as_str())
            }

            Some(builder::Newline(Some(comment)))
        }

        Some(Token::Newline) => {
            drop(mp);
            iter.next();
            Some(builder::Newline(None))
        }

        _ => None,
    }
}

#[cfg(test)]
mod test {
    use crate::ast::builder;
    use crate::parse::iter::TokenIter;
    use crate::token::Token;

    fn test(mut start: Vec<Token>, remaining: &[Token]) -> Vec<builder::Newline> {
        start.extend_from_slice(remaining);

        let mut iter = TokenIter::new(start);
        let ret = super::linebreak(&mut iter);

        assert_eq!(remaining, iter.collect::<Vec<_>>());
        ret
    }

    #[test]
    fn newline_not_greedy() {
        let mut start = vec![Token::Whitespace(" ".into()), Token::Newline];

        let remaining = &[
            Token::Whitespace(" ".into()),
            Token::Newline,
            Token::Whitespace(" ".into()),
        ];

        start.extend_from_slice(remaining);

        let mut iter = TokenIter::new(start);
        assert_eq!(Some(builder::Newline(None)), super::newline(&mut iter));
        assert_eq!(remaining, iter.collect::<Vec<_>>().as_slice());
    }

    #[test]
    fn empty() {
        let ret = test(vec![], &[]);
        assert_eq!(ret, vec!());
    }

    #[test]
    fn invalid() {
        let ret = test(
            vec![],
            &[
                Token::Literal("hello".into()),
                Token::Whitespace(" ".into()),
                Token::Literal("world".into()),
            ],
        );

        assert_eq!(ret, vec!());
    }

    #[test]
    fn eof() {
        let ret = test(
            vec![
                Token::Pound,
                Token::Literal("com".into()),
                Token::Literal("ment".into()),
            ],
            &[],
        );

        assert_eq!(vec!(builder::Newline(Some("#comment".into()))), ret);
    }

    #[test]
    fn comments_and_whitespace() {
        let ret = test(
            vec![
                Token::Newline,
                Token::Whitespace(" \t".into()),
                Token::Newline,
                Token::Whitespace(" \t".into()),
                Token::Pound,
                Token::Whitespace(" ".into()),
                Token::Literal("comment1".into()),
                Token::Newline,
                Token::Pound,
                Token::Literal("comment2".into()),
                Token::Newline,
                Token::Pound,
                Token::Literal("comment3".into()),
                Token::Pound,
                Token::Literal("comment4".into()),
                Token::Newline,
            ],
            &[],
        );

        let expected = vec![
            builder::Newline(None),
            builder::Newline(None),
            builder::Newline(Some("# comment1".into())),
            builder::Newline(Some("#comment2".into())),
            builder::Newline(Some("#comment3#comment4".into())),
        ];

        assert_eq!(expected, ret);
    }

    #[test]
    fn comment_quoting_insignificant_in() {
        let ret = test(
            vec![
                Token::Pound,
                Token::Literal("unclosed".into()),
                Token::Whitespace(" ".into()),
                Token::SingleQuote,
                Token::Whitespace(" ".into()),
                Token::Literal("comment".into()),
                Token::Newline,
                Token::Pound,
                Token::Literal("unclosed".into()),
                Token::Whitespace(" ".into()),
                Token::DoubleQuote,
                Token::Whitespace(" ".into()),
                Token::Literal("comment".into()),
                Token::Newline,
                Token::Pound,
                Token::Literal("unclosed".into()),
                Token::Whitespace(" ".into()),
                Token::Backtick,
                Token::Whitespace(" ".into()),
                Token::Literal("comment".into()),
                Token::Newline,
                Token::Pound,
                Token::Literal("unclosed".into()),
                Token::Whitespace(" ".into()),
                Token::ParenOpen,
                Token::Whitespace(" ".into()),
                Token::Literal("comment".into()),
                Token::Newline,
                Token::Pound,
                Token::Literal("unclosed".into()),
                Token::Whitespace(" ".into()),
                Token::Dollar,
                Token::ParenOpen,
                Token::Whitespace(" ".into()),
                Token::Literal("comment".into()),
                Token::Newline,
            ],
            &[],
        );

        let expected = vec![
            builder::Newline(Some("#unclosed ' comment".into())),
            builder::Newline(Some("#unclosed \" comment".into())),
            builder::Newline(Some("#unclosed ` comment".into())),
            builder::Newline(Some("#unclosed ( comment".into())),
            builder::Newline(Some("#unclosed $( comment".into())),
        ];

        assert_eq!(expected, ret);
    }

    #[test]
    fn comment_escaping_newline_insignificant() {
        let ret = test(
            vec![
                Token::Pound,
                Token::Literal("comment1".into()),
                Token::Backslash,
                Token::Newline,
                Token::Pound,
                Token::Literal("comment2".into()),
                Token::Newline,
            ],
            &[],
        );

        let expected = vec![
            builder::Newline(Some("#comment1\\".into())),
            builder::Newline(Some("#comment2".into())),
        ];

        assert_eq!(expected, ret);
    }

    #[test]
    fn comment_eof() {
        let ret = test(vec![Token::Pound, Token::Literal("comment".into())], &[]);

        let expected = vec![builder::Newline(Some("#comment".into()))];

        assert_eq!(expected, ret);
    }

    #[test]
    fn comment_cannot_escape_pound() {
        let ret = test(
            vec![],
            &[
                Token::Backslash,
                Token::Pound,
                Token::Literal("comment".into()),
            ],
        );

        assert_eq!(ret, vec!());
    }
}
