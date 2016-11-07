extern crate shell_lang;

use shell_lang::ast::*;
use shell_lang::ast::builder::*;
use shell_lang::ast::CompoundCommandKind::*;
use shell_lang::ast::PipeableCommand::*;
use shell_lang::parse::*;
use shell_lang::parse::ParseError::*;
use shell_lang::token::Token;

mod parse_support;
use parse_support::*;

#[test]
fn test_linebreak_valid_with_comments_and_whitespace() {
    let mut p = make_parser("\n\t\t\t\n # comment1\n#comment2\n   \n");
    assert_eq!(p.linebreak(), vec!(
            Newline(None),
            Newline(None),
            Newline(Some(String::from("# comment1"))),
            Newline(Some(String::from("#comment2"))),
            Newline(None)
        )
    );
}

#[test]
fn test_linebreak_valid_empty() {
    let mut p = make_parser("");
    assert_eq!(p.linebreak(), vec!());
}

#[test]
fn test_linebreak_valid_nonnewline() {
    let mut p = make_parser("hello world");
    assert_eq!(p.linebreak(), vec!());
}

#[test]
fn test_linebreak_valid_eof_instead_of_newline() {
    let mut p = make_parser("#comment");
    assert_eq!(p.linebreak(), vec!(Newline(Some(String::from("#comment")))));
}

#[test]
fn test_linebreak_single_quote_insiginificant() {
    let mut p = make_parser("#unclosed quote ' comment");
    assert_eq!(p.linebreak(), vec!(Newline(Some(String::from("#unclosed quote ' comment")))));
}

#[test]
fn test_linebreak_double_quote_insiginificant() {
    let mut p = make_parser("#unclosed quote \" comment");
    assert_eq!(p.linebreak(), vec!(Newline(Some(String::from("#unclosed quote \" comment")))));
}

#[test]
fn test_linebreak_escaping_newline_insignificant() {
    let mut p = make_parser("#comment escapes newline\\\n");
    assert_eq!(p.linebreak(), vec!(Newline(Some(String::from("#comment escapes newline\\")))));
}

#[test]
fn test_skip_whitespace_preserve_newline() {
    let mut p = make_parser("    \t\t \t \t\n   ");
    p.skip_whitespace();
    assert_eq!(p.linebreak().len(), 1);
}

#[test]
fn test_skip_whitespace_preserve_comments() {
    let mut p = make_parser("    \t\t \t \t#comment\n   ");
    p.skip_whitespace();
    assert_eq!(p.linebreak().pop().unwrap(), Newline(Some(String::from("#comment"))));
}

#[test]
fn test_skip_whitespace_comments_capture_all_up_to_newline() {
    let mut p = make_parser("#comment&&||;;()<<-\n");
    assert_eq!(p.linebreak().pop().unwrap(), Newline(Some(String::from("#comment&&||;;()<<-"))));
}

#[test]
fn test_skip_whitespace_comments_may_end_with_eof() {
    let mut p = make_parser("#comment");
    assert_eq!(p.linebreak().pop().unwrap(), Newline(Some(String::from("#comment"))));
}

#[test]
fn test_skip_whitespace_skip_escapes_dont_affect_newlines() {
    let mut p = make_parser("  \t \\\n  \\\n#comment\n");
    p.skip_whitespace();
    assert_eq!(p.linebreak().pop().unwrap(), Newline(Some(String::from("#comment"))));
}

#[test]
fn test_skip_whitespace_skips_escaped_newlines() {
    let mut p = make_parser("\\\n\\\n   \\\n");
    p.skip_whitespace();
    assert_eq!(p.linebreak(), vec!());
}

#[test]
fn test_and_or_correct_associativity() {
    let mut p = make_parser("foo || bar && baz");
    let correct = CommandList {
        first: ListableCommand::Single(Simple(cmd_simple("foo"))),
        rest: vec!(
            AndOr::Or(ListableCommand::Single(Simple(cmd_simple("bar")))),
            AndOr::And(ListableCommand::Single(Simple(cmd_simple("baz")))),
        ),
    };
    assert_eq!(correct, p.and_or_list().unwrap());
}

#[test]
fn test_and_or_valid_with_newlines_after_operator() {
    let mut p = make_parser("foo ||\n\n\n\nbar && baz");
    let correct = CommandList {
        first: ListableCommand::Single(Simple(cmd_simple("foo"))),
        rest: vec!(
            AndOr::Or(ListableCommand::Single(Simple(cmd_simple("bar")))),
            AndOr::And(ListableCommand::Single(Simple(cmd_simple("baz")))),
        ),
    };
    assert_eq!(correct, p.and_or_list().unwrap());
}

#[test]
fn test_and_or_invalid_with_newlines_before_operator() {
    let mut p = make_parser("foo || bar\n\n&& baz");
    p.and_or_list().unwrap(); // Successful parse Or(foo, bar)
    // Fail to parse "&& baz" which is an error
    assert_eq!(Err(Unexpected(Token::AndIf, src(12, 3, 1))), p.complete_command());
}

#[test]
fn test_pipeline_valid_bang() {
    let mut p = make_parser("! foo | bar | baz");
    let correct = CommandList {
        first: ListableCommand::Pipe(true, vec!(
            Simple(cmd_simple("foo")),
            Simple(cmd_simple("bar")),
            Simple(cmd_simple("baz")),
        )),
        rest: vec!(),
    };
    assert_eq!(correct, p.and_or_list().unwrap());
}

#[test]
fn test_pipeline_valid_bangs_in_and_or() {
    let mut p = make_parser("! foo | bar || ! baz && ! foobar");
    let correct = CommandList {
        first: ListableCommand::Pipe(true, vec!(
            Simple(cmd_simple("foo")),
            Simple(cmd_simple("bar"))
        )),
        rest: vec!(
            AndOr::Or(ListableCommand::Pipe(true, vec!(
                Simple(cmd_simple("baz")),
            ))),
            AndOr::And(ListableCommand::Pipe(true, vec!(
                Simple(cmd_simple("foobar")),
            ))),
        ),
    };
    assert_eq!(correct, p.and_or_list().unwrap());
}

#[test]
fn test_pipeline_no_bang_single_cmd_optimize_wrapper_out() {
    let mut p = make_parser("foo");
    let parse = p.pipeline().unwrap();
    if let ListableCommand::Pipe(..) = parse {
        panic!("Parser::pipeline should not create a wrapper if no ! present and only a single command");
    }
}

#[test]
fn test_pipeline_invalid_multiple_bangs_in_same_pipeline() {
    let mut p = make_parser("! foo | bar | ! baz");
    assert_eq!(Err(Unexpected(Token::Bang, src(14, 1, 15))), p.pipeline());
}

#[test]
fn test_comment_cannot_start_mid_whitespace_delimited_word() {
    let mut p = make_parser("hello#world");
    let w = p.word().unwrap().expect("no valid word was discovered");
    assert_eq!(w, word("hello#world"));
}

#[test]
fn test_comment_can_start_if_whitespace_before_pound() {
    let mut p = make_parser("hello #world");
    p.word().unwrap().expect("no valid word was discovered");
    let comment = p.linebreak();
    assert_eq!(comment, vec!(Newline(Some(String::from("#world")))));
}

#[test]
fn test_do_group_valid() {
    let mut p = make_parser("do foo\nbar; baz\n#comment\n done");
    let correct = CommandGroup {
        commands: vec!(cmd("foo"), cmd("bar"), cmd("baz")),
        trailing_comments: vec!(Newline(Some("#comment".into()))),
    };
    assert_eq!(correct, p.do_group().unwrap());
}

#[test]
fn test_do_group_invalid_missing_separator() {
    let mut p = make_parser("do foo\nbar; baz done");
    assert_eq!(Err(IncompleteCmd("do", src(0,1,1), "done", src(20,2,14))), p.do_group());
}

#[test]
fn test_do_group_valid_keyword_delimited_by_separator() {
    let mut p = make_parser("do foo done; done");
    let correct = CommandGroup {
        commands: vec!(cmd_args("foo", &["done"])),
        trailing_comments: vec!(),
    };
    assert_eq!(correct, p.do_group().unwrap());
}

#[test]
fn test_do_group_invalid_missing_keyword() {
    let mut p = make_parser("foo\nbar; baz; done");
    assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(0,1,1))), p.do_group());
    let mut p = make_parser("do foo\nbar; baz");
    assert_eq!(Err(IncompleteCmd("do", src(0,1,1), "done", src(15,2,9))), p.do_group());
}

#[test]
fn test_do_group_invalid_quoted() {
    let cmds = [
        ("'do' foo\nbar; baz; done",   Unexpected(Token::SingleQuote, src(0, 1, 1))),
        ("do foo\nbar; baz; 'done'",   IncompleteCmd("do", src(0,1,1), "done", src(23,2,17))),
        ("\"do\" foo\nbar; baz; done", Unexpected(Token::DoubleQuote, src(0, 1, 1))),
        ("do foo\nbar; baz; \"done\"", IncompleteCmd("do", src(0,1,1), "done", src(23,2,17))),
    ];

    for &(c, ref e) in cmds.into_iter() {
        match make_parser(c).do_group() {
            Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       c, e, err);
            },
        }
    }
}

#[test]
fn test_do_group_invalid_concat() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("d")),
        Token::Literal(String::from("o")),
        Token::Newline,
        Token::Literal(String::from("foo")),
        Token::Newline,
        Token::Literal(String::from("done")),
    ));
    assert_eq!(Err(Unexpected(Token::Literal(String::from("d")), src(0,1,1))), p.do_group());
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("do")),
        Token::Newline,
        Token::Literal(String::from("foo")),
        Token::Newline,
        Token::Literal(String::from("do")),
        Token::Literal(String::from("ne")),
    ));
    assert_eq!(Err(IncompleteCmd("do", src(0,1,1), "done", src(11,3,5))), p.do_group());
}

#[test]
fn test_do_group_should_recognize_literals_and_names() {
    for do_tok in vec!(Token::Literal(String::from("do")), Token::Name(String::from("do"))) {
        for done_tok in vec!(Token::Literal(String::from("done")), Token::Name(String::from("done"))) {
            let mut p = make_parser_from_tokens(vec!(
                do_tok.clone(),
                Token::Newline,
                Token::Literal(String::from("foo")),
                Token::Newline,
                done_tok
            ));
            p.do_group().unwrap();
        }
    }
}

#[test]
fn test_do_group_invalid_missing_body() {
    let mut p = make_parser("do\ndone");
    assert_eq!(Err(Unexpected(Token::Name("done".into()), src(3,2,1))), p.do_group());
}

#[test]
fn test_loop_command_while_valid() {
    let mut p = make_parser("while guard1; guard2;\n#guard_comment\n do foo\nbar; baz\n#body_comment\n done");
    let (until, GuardBodyPairGroup { guard, body }) = p.loop_command().unwrap();

    let correct_guard = CommandGroup {
        commands: vec!(cmd("guard1"), cmd("guard2")),
        trailing_comments: vec!(Newline(Some("#guard_comment".into()))),
    };
    let correct_body = CommandGroup {
        commands: vec!(cmd("foo"), cmd("bar"), cmd("baz")),
        trailing_comments: vec!(Newline(Some("#body_comment".into()))),
    };

    assert_eq!(until, LoopKind::While);
    assert_eq!(correct_guard, guard);
    assert_eq!(correct_body, body);
}

#[test]
fn test_loop_command_until_valid() {
    let mut p = make_parser("until guard1; guard2;\n#guard_comment\n do foo\nbar; baz\n#body_comment\n done");
    let (until, GuardBodyPairGroup { guard, body }) = p.loop_command().unwrap();

    let correct_guard = CommandGroup {
        commands: vec!(cmd("guard1"), cmd("guard2")),
        trailing_comments: vec!(Newline(Some("#guard_comment".into()))),
    };
    let correct_body = CommandGroup {
        commands: vec!(cmd("foo"), cmd("bar"), cmd("baz")),
        trailing_comments: vec!(Newline(Some("#body_comment".into()))),
    };

    assert_eq!(until, LoopKind::Until);
    assert_eq!(correct_guard, guard);
    assert_eq!(correct_body, body);
}

#[test]
fn test_loop_command_invalid_missing_separator() {
    let mut p = make_parser("while guard do foo\nbar; baz; done");
    assert_eq!(Err(IncompleteCmd("while", src(0,1,1), "do", src(33,2,15))), p.loop_command());
    let mut p = make_parser("while guard; do foo\nbar; baz done");
    assert_eq!(Err(IncompleteCmd("do", src(13,1,14), "done", src(33,2,14))), p.loop_command());
}

#[test]
fn test_loop_command_invalid_missing_keyword() {
    let mut p = make_parser("guard; do foo\nbar; baz; done");
    assert_eq!(Err(Unexpected(Token::Name(String::from("guard")), src(0,1,1))), p.loop_command());
}

#[test]
fn test_loop_command_invalid_missing_guard() {
    // With command separator between loop and do keywords
    let mut p = make_parser("while; do foo\nbar; baz; done");
    assert_eq!(Err(Unexpected(Token::Semi, src(5, 1, 6))), p.loop_command());
    let mut p = make_parser("until; do foo\nbar; baz; done");
    assert_eq!(Err(Unexpected(Token::Semi, src(5, 1, 6))), p.loop_command());

    // Without command separator between loop and do keywords
    let mut p = make_parser("while do foo\nbar; baz; done");
    assert_eq!(Err(Unexpected(Token::Name(String::from("do")), src(6, 1, 7))), p.loop_command());
    let mut p = make_parser("until do foo\nbar; baz; done");
    assert_eq!(Err(Unexpected(Token::Name(String::from("do")), src(6, 1, 7))), p.loop_command());
}

#[test]
fn test_loop_command_invalid_quoted() {
    let cmds = [
        ("'while' guard do foo\nbar; baz; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("'until' guard do foo\nbar; baz; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("\"while\" guard do foo\nbar; baz; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("\"until\" guard do foo\nbar; baz; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
    ];

    for &(c, ref e) in cmds.into_iter() {
        match make_parser(c).loop_command() {
            Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       c, e, err);
            },
        }
    }
}

#[test]
fn test_loop_command_invalid_concat() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("whi")),
        Token::Literal(String::from("le")),
        Token::Newline,
        Token::Literal(String::from("guard")),
        Token::Newline,
        Token::Literal(String::from("do")),
        Token::Literal(String::from("foo")),
        Token::Newline,
        Token::Literal(String::from("done")),
    ));
    assert_eq!(Err(Unexpected(Token::Literal(String::from("whi")), src(0,1,1))), p.loop_command());
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("un")),
        Token::Literal(String::from("til")),
        Token::Newline,
        Token::Literal(String::from("guard")),
        Token::Newline,
        Token::Literal(String::from("do")),
        Token::Literal(String::from("foo")),
        Token::Newline,
        Token::Literal(String::from("done")),
    ));
    assert_eq!(Err(Unexpected(Token::Literal(String::from("un")), src(0,1,1))), p.loop_command());
}

#[test]
fn test_loop_command_should_recognize_literals_and_names() {
    for kw in vec!(
        Token::Literal(String::from("while")),
        Token::Name(String::from("while")),
        Token::Literal(String::from("until")),
        Token::Name(String::from("until")))
    {
        let mut p = make_parser_from_tokens(vec!(
            kw,
            Token::Newline,
            Token::Literal(String::from("guard")),
            Token::Newline,
            Token::Literal(String::from("do")),
            Token::Newline,
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Literal(String::from("done")),
        ));
        p.loop_command().unwrap();
    }
}

#[test]
fn test_braces_literal_unless_brace_group_expected() {
    let source = "echo {} } {";
    let mut p = make_parser(source);
    assert_eq!(p.word().unwrap().unwrap(), word("echo"));
    assert_eq!(p.word().unwrap().unwrap(), word("{}"));
    assert_eq!(p.word().unwrap().unwrap(), word("}"));
    assert_eq!(p.word().unwrap().unwrap(), word("{"));

    let correct = Some(cmd_args("echo", &["{}", "}", "{"]));
    assert_eq!(correct, make_parser(source).complete_command().unwrap());
}

#[test]
fn test_compound_command_delegates_valid_commands_brace() {
    let correct = CompoundCommand {
        kind: Brace(vec!(cmd("foo"))),
        io: vec!(),
    };
    assert_eq!(correct, make_parser("{ foo; }").compound_command().unwrap());
}

#[test]
fn test_compound_command_delegates_valid_commands_subshell() {
    let commands = [
        "(foo)",
        "( foo)",
    ];

    let correct = CompoundCommand {
        kind: Subshell(vec!(cmd("foo"))),
        io: vec!(),
    };

    for cmd in &commands {
        match make_parser(cmd).compound_command() {
            Ok(ref result) if result == &correct => {},
            Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
            Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
        }
    }
}

#[test]
fn test_compound_command_delegates_valid_commands_while() {
    let correct = CompoundCommand {
        kind: While(GuardBodyPair {
            guard: vec!(cmd("guard")),
            body: vec!(cmd("foo")),
        }),
        io: vec!(),
    };
    assert_eq!(correct, make_parser("while guard; do foo; done").compound_command().unwrap());
}

#[test]
fn test_compound_command_delegates_valid_commands_until() {
    let correct = CompoundCommand {
        kind: Until(GuardBodyPair {
            guard: vec!(cmd("guard")),
            body: vec!(cmd("foo")),
        }),
        io: vec!(),
    };
    assert_eq!(correct, make_parser("until guard; do foo; done").compound_command().unwrap());
}

#[test]
fn test_compound_command_delegates_valid_commands_for() {
    let correct = CompoundCommand {
        kind: For {
            var: String::from("var"),
            words: Some(vec!()),
            body: vec!(cmd("foo")),
        },
        io: vec!(),
    };
    assert_eq!(correct, make_parser("for var in; do foo; done").compound_command().unwrap());
}

#[test]
fn test_compound_command_delegates_valid_commands_if() {
    let correct = CompoundCommand {
        kind: If {
            conditionals: vec!(GuardBodyPair {
                guard: vec!(cmd("guard")),
                body: vec!(cmd("body")),
            }),
            else_branch: None,
        },
        io: vec!(),
    };
    assert_eq!(correct, make_parser("if guard; then body; fi").compound_command().unwrap());
}

#[test]
fn test_compound_command_delegates_valid_commands_case() {
    let correct = CompoundCommand {
        kind: Case {
            word: word("foo"),
            arms: vec!(),
        },
        io: vec!(),
    };
    assert_eq!(correct, make_parser("case foo in esac").compound_command().unwrap());
}

#[test]
fn test_compound_command_errors_on_quoted_commands() {
    let cases = [
        // { is a reserved word, thus concatenating it essentially "quotes" it
        // `compound_command` doesn't know or care enough to specify that "foo" is
        // the problematic token instead of {, however, callers who are smart enough
        // to expect a brace command would be aware themselves that no such valid
        // command actually exists. TL;DR: it's okay for `compound_command` to blame {
        ("{foo; }",                      Unexpected(Token::CurlyOpen,   src(0,1,1))),
        ("'{' foo; }",                   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("'(' foo; )",                   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("'while' guard do foo; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("'until' guard do foo; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("'if' guard; then body; fi",    Unexpected(Token::SingleQuote, src(0,1,1))),
        ("'for' var in; do foo; done",   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("'case' foo in esac",           Unexpected(Token::SingleQuote, src(0,1,1))),
        ("\"{\" foo; }",                 Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("\"(\" foo; )",                 Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("\"while\" guard do foo; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("\"until\" guard do foo; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("\"if\" guard; then body; fi",  Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("\"for\" var in; do foo; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("\"case\" foo in esac",         Unexpected(Token::DoubleQuote, src(0,1,1))),
    ];

    for &(src, ref e) in &cases {
        match make_parser(src).compound_command() {
            Ok(result) =>
                panic!("Parse::compound_command unexpectedly succeeded parsing \"{}\" with result:\n{:#?}",
                       src, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       src, e, err);
            },
        }
    }
}

#[test]
fn test_compound_command_captures_redirections_after_command() {
    let cases = [
        "{ foo; } 1>>out <& 2 2>&-",
        "( foo; ) 1>>out <& 2 2>&-",
        "while guard; do foo; done 1>>out <& 2 2>&-",
        "until guard; do foo; done 1>>out <& 2 2>&-",
        "if guard; then body; fi 1>>out <& 2 2>&-",
        "for var in; do foo; done 1>>out <& 2 2>&-",
        "case foo in esac 1>>out <& 2 2>&-",
    ];

    for cmd in &cases {
        match make_parser(cmd).compound_command() {
            Ok(CompoundCommand { io, .. }) => assert_eq!(io, vec!(
                Redirect::Append(Some(1), word("out")),
                Redirect::DupRead(None, word("2")),
                Redirect::DupWrite(Some(2), word("-")),
            )),

            Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
        }
    }
}

#[test]
fn test_compound_command_should_delegate_literals_and_names_loop() {
    for kw in vec!(
        Token::Literal(String::from("while")),
        Token::Name(String::from("while")),
        Token::Literal(String::from("until")),
        Token::Name(String::from("until")))
    {
        let mut p = make_parser_from_tokens(vec!(
            kw,
            Token::Newline,
            Token::Literal(String::from("guard")),
            Token::Newline,
            Token::Literal(String::from("do")),
            Token::Newline,
            Token::Literal(String::from("foo")),
            Token::Newline,
            Token::Literal(String::from("done")),
        ));
        p.compound_command().unwrap();
    }
}

#[test]
fn test_compound_command_should_delegate_literals_and_names_if() {
    for if_tok in vec!(Token::Literal(String::from("if")), Token::Name(String::from("if"))) {
        for then_tok in vec!(Token::Literal(String::from("then")), Token::Name(String::from("then"))) {
            for elif_tok in vec!(Token::Literal(String::from("elif")), Token::Name(String::from("elif"))) {
                for else_tok in vec!(Token::Literal(String::from("else")), Token::Name(String::from("else"))) {
                    for fi_tok in vec!(Token::Literal(String::from("fi")), Token::Name(String::from("fi"))) {
                        let mut p = make_parser_from_tokens(vec!(
                                if_tok.clone(),
                                Token::Whitespace(String::from(" ")),

                                Token::Literal(String::from("guard1")),
                                Token::Newline,

                                then_tok.clone(),
                                Token::Newline,
                                Token::Literal(String::from("body1")),

                                elif_tok.clone(),
                                Token::Whitespace(String::from(" ")),

                                Token::Literal(String::from("guard2")),
                                Token::Newline,
                                then_tok.clone(),
                                Token::Whitespace(String::from(" ")),
                                Token::Literal(String::from("body2")),

                                else_tok.clone(),
                                Token::Whitespace(String::from(" ")),

                                Token::Whitespace(String::from(" ")),
                                Token::Literal(String::from("else part")),
                                Token::Newline,

                                fi_tok,
                        ));
                        p.compound_command().unwrap();
                    }
                }
            }
        }
    }
}

#[test]
fn test_compound_command_should_delegate_literals_and_names_for() {
    for for_tok in vec!(Token::Literal(String::from("for")), Token::Name(String::from("for"))) {
        for in_tok in vec!(Token::Literal(String::from("in")), Token::Name(String::from("in"))) {
            let mut p = make_parser_from_tokens(vec!(
                for_tok.clone(),
                Token::Whitespace(String::from(" ")),

                Token::Name(String::from("var")),
                Token::Whitespace(String::from(" ")),

                in_tok.clone(),
                Token::Whitespace(String::from(" ")),
                Token::Literal(String::from("one")),
                Token::Whitespace(String::from(" ")),
                Token::Literal(String::from("two")),
                Token::Whitespace(String::from(" ")),
                Token::Literal(String::from("three")),
                Token::Whitespace(String::from(" ")),
                Token::Newline,

                Token::Literal(String::from("do")),
                Token::Whitespace(String::from(" ")),

                Token::Literal(String::from("echo")),
                Token::Whitespace(String::from(" ")),
                Token::Dollar,
                Token::Name(String::from("var")),
                Token::Newline,

                Token::Literal(String::from("done")),
            ));
            p.compound_command().unwrap();
        }
    }
}

#[test]
fn test_compound_command_should_delegate_literals_and_names_case() {
    let case_str = String::from("case");
    let in_str   = String::from("in");
    let esac_str = String::from("esac");
    for case_tok in vec!(Token::Literal(case_str.clone()), Token::Name(case_str.clone())) {
        for in_tok in vec!(Token::Literal(in_str.clone()), Token::Name(in_str.clone())) {
            for esac_tok in vec!(Token::Literal(esac_str.clone()), Token::Name(esac_str.clone())) {
                let mut p = make_parser_from_tokens(vec!(
                    case_tok.clone(),
                    Token::Whitespace(String::from(" ")),

                    Token::Literal(String::from("foo")),
                    Token::Literal(String::from("bar")),

                    Token::Whitespace(String::from(" ")),
                    in_tok.clone(),
                    Token::Whitespace(String::from(" ")),

                    Token::Literal(String::from("foo")),
                    Token::ParenClose,
                    Token::Newline,
                    Token::Literal(String::from("echo")),
                    Token::Whitespace(String::from(" ")),
                    Token::Literal(String::from("foo")),
                    Token::Newline,
                    Token::Newline,
                    Token::DSemi,

                    esac_tok
                ));
                p.compound_command().unwrap();
            }
        }
    }
}

#[test]
fn ensure_parse_errors_are_send_and_sync() {
    fn send_and_sync<T: Send + Sync>() {}
    send_and_sync::<ParseError<()>>();
}

#[test]
fn ensure_parser_could_be_send_and_sync() {
    fn send_and_sync<T: Send + Sync>() {}
    send_and_sync::<Parser<::std::vec::IntoIter<Token>, StringBuilder>>();
}
