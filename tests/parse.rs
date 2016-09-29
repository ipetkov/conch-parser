extern crate shell_lang;

use std::rc::Rc;

use shell_lang::ast::*;
use shell_lang::ast::builder::*;
use shell_lang::ast::Command::*;
use shell_lang::ast::ComplexWord::*;
use shell_lang::ast::CompoundCommandKind::*;
use shell_lang::ast::PipeableCommand::*;
use shell_lang::ast::SimpleWord::*;
use shell_lang::lexer::Lexer;
use shell_lang::parse::*;
use shell_lang::parse::ParseError::*;
use shell_lang::token::Token;

fn lit(s: &str) -> Word {
    Word::Simple(Literal(String::from(s)))
}

fn escaped(s: &str) -> Word {
    Word::Simple(Escaped(String::from(s)))
}

fn subst(s: ParameterSubstitution) -> Word {
    Word::Simple(Subst(Box::new(s)))
}

fn single_quoted(s: &str) -> TopLevelWord {
    TopLevelWord(Single(Word::SingleQuoted(String::from(s))))
}

fn double_quoted(s: &str) -> TopLevelWord {
    TopLevelWord(Single(Word::DoubleQuoted(vec!(Literal(String::from(s))))))
}

fn word(s: &str) -> TopLevelWord {
    TopLevelWord(Single(lit(s)))
}

fn word_escaped(s: &str) -> TopLevelWord {
    TopLevelWord(Single(escaped(s)))
}

fn word_subst(s: ParameterSubstitution) -> TopLevelWord {
    TopLevelWord(Single(subst(s)))
}

fn word_param(p: Parameter) -> TopLevelWord {
    TopLevelWord(Single(Word::Simple(Param(p))))
}

fn make_parser(src: &str) -> DefaultParser<Lexer<::std::str::Chars>> {
    DefaultParser::new(Lexer::new(src.chars()))
}

fn make_parser_from_tokens(src: Vec<Token>) -> DefaultParser<::std::vec::IntoIter<Token>> {
    DefaultParser::new(src.into_iter())
}

fn cmd_args_simple(cmd: &str, args: &[&str]) -> Box<SimpleCommand> {
    let cmd = word(cmd);
    let args = args.iter().map(|&a| word(a)).collect();

    Box::new(SimpleCommand {
        cmd: Some((cmd, args)),
        vars: vec!(),
        io: vec!(),
    })
}

fn cmd_simple(cmd: &str) -> Box<SimpleCommand> {
    cmd_args_simple(cmd, &[])
}

fn cmd_args(cmd: &str, args: &[&str]) -> TopLevelCommand {
    TopLevelCommand(List(CommandList {
        first: ListableCommand::Single(Simple(cmd_args_simple(cmd, args))),
        rest: vec!(),
    }))
}

fn cmd(cmd: &str) -> TopLevelCommand {
    cmd_args(cmd, &[])
}

fn cmd_from_simple(cmd: SimpleCommand) -> TopLevelCommand {
    TopLevelCommand(List(CommandList {
        first: ListableCommand::Single(Simple(Box::new(cmd))),
        rest: vec!(),
    }))
}

fn src(byte: usize, line: usize, col: usize) -> SourcePos {
    SourcePos {
        byte: byte,
        line: line,
        col: col,
    }
}

struct SimpleCommandFragments {
    cmd: Option<(TopLevelWord, Vec<TopLevelWord>)>,
    vars: Vec<(String, Option<TopLevelWord>)>,
    io: Vec<Redirect>,
}

fn sample_simple_command() -> SimpleCommandFragments {
    SimpleCommandFragments {
        cmd: Some((word("foo"), vec!(
            word("bar"),
            word("baz"),
        ))),
        vars: vec!(
            (String::from("var"), Some(word("val"))),
            (String::from("ENV"), Some(word("true"))),
            (String::from("BLANK"), None),
        ),
        io: vec!(
            Redirect::Clobber(Some(2), word("clob")),
            Redirect::ReadWrite(Some(3), word("rw")),
            Redirect::Read(None, word("in")),
        ),
    }
}

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
fn test_complete_command_job() {
    let mut p = make_parser("foo && bar & baz");
    let cmd1 = p.complete_command().unwrap().expect("failed to parse first command");
    let cmd2 = p.complete_command().unwrap().expect("failed to parse second command");

    let correct1 = TopLevelCommand(Job(CommandList {
        first: ListableCommand::Single(Simple(cmd_simple("foo"))),
        rest: vec!(
            AndOr::And(ListableCommand::Single(Simple(cmd_simple("bar"))))
        ),
    }));
    let correct2 = cmd("baz");

    assert_eq!(correct1, cmd1);
    assert_eq!(correct2, cmd2);
}

#[test]
fn test_complete_command_non_eager_parse() {
    let mut p = make_parser("foo && bar; baz\n\nqux");
    let cmd1 = p.complete_command().unwrap().expect("failed to parse first command");
    let cmd2 = p.complete_command().unwrap().expect("failed to parse second command");
    let cmd3 = p.complete_command().unwrap().expect("failed to parse third command");

    let correct1 = TopLevelCommand(List(CommandList {
        first: ListableCommand::Single(Simple(cmd_simple("foo"))),
        rest: vec!(
            AndOr::And(ListableCommand::Single(Simple(cmd_simple("bar"))))
        ),
    }));
    let correct2 = cmd("baz");
    let correct3 = cmd("qux");

    assert_eq!(correct1, cmd1);
    assert_eq!(correct2, cmd2);
    assert_eq!(correct3, cmd3);
}

#[test]
fn test_complete_command_valid_no_input() {
    let mut p = make_parser("");
    p.complete_command().expect("no input caused an error");
}

#[test]
fn test_parameter_short() {
    let words = vec!(
        Parameter::At,
        Parameter::Star,
        Parameter::Pound,
        Parameter::Question,
        Parameter::Dash,
        Parameter::Dollar,
        Parameter::Bang,
        Parameter::Positional(3),
    );

    let mut p = make_parser("$@$*$#$?$-$$$!$3$");
    for param in words {
        assert_eq!(p.parameter().unwrap(), word_param(param));
    }

    assert_eq!(word("$"), p.parameter().unwrap());
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_short_in_curlies() {
    let words = vec!(
        Parameter::At,
        Parameter::Star,
        Parameter::Pound,
        Parameter::Question,
        Parameter::Dash,
        Parameter::Dollar,
        Parameter::Bang,
        Parameter::Var(String::from("foo")),
        Parameter::Positional(3),
        Parameter::Positional(1000),
    );

    let mut p = make_parser("${@}${*}${#}${?}${-}${$}${!}${foo}${3}${1000}");
    for param in words {
        assert_eq!(p.parameter().unwrap(), word_param(param));
    }

    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_command_substitution() {
    let correct = word_subst(ParameterSubstitution::Command(vec!(
        cmd_args("echo", &["hello"]),
        cmd_args("echo", &["world"]),
    )));

    assert_eq!(correct, make_parser("$(echo hello; echo world)").parameter().unwrap());
}

#[test]
fn test_parameter_command_substitution_valid_empty_substitution() {
    let correct = word_subst(ParameterSubstitution::Command(vec!()));
    assert_eq!(correct, make_parser("$()").parameter().unwrap());
    assert_eq!(correct, make_parser("$(     )").parameter().unwrap());
    assert_eq!(correct, make_parser("$(\n\n)").parameter().unwrap());
}

#[test]
fn test_parameter_literal_dollar_if_no_param() {
    let mut p = make_parser("$%asdf");
    assert_eq!(word("$"), p.parameter().unwrap());
    assert_eq!(p.word().unwrap().unwrap(), word("%asdf"));
}

#[test]
fn test_parameter_substitution() {
    let words = vec!(
        ParameterSubstitution::Len(Parameter::At),
        ParameterSubstitution::Len(Parameter::Star),
        ParameterSubstitution::Len(Parameter::Pound),
        ParameterSubstitution::Len(Parameter::Question),
        ParameterSubstitution::Len(Parameter::Dash),
        ParameterSubstitution::Len(Parameter::Dollar),
        ParameterSubstitution::Len(Parameter::Bang),
        ParameterSubstitution::Len(Parameter::Var(String::from("foo"))),
        ParameterSubstitution::Len(Parameter::Positional(3)),
        ParameterSubstitution::Len(Parameter::Positional(1000)),
        ParameterSubstitution::Command(vec!(cmd_args("echo", &["foo"]))),
    );

    let mut p = make_parser("${#@}${#*}${##}${#?}${#-}${#$}${#!}${#foo}${#3}${#1000}$(echo foo)");
    for param in words {
        let correct = word_subst(param);
        assert_eq!(correct, p.parameter().unwrap());
    }

    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_smallest_suffix() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let word = word("foo");

    let substs = vec!(
        RemoveSmallestSuffix(At, Some(word.clone())),
        RemoveSmallestSuffix(Star, Some(word.clone())),
        RemoveSmallestSuffix(Pound, Some(word.clone())),
        RemoveSmallestSuffix(Question, Some(word.clone())),
        RemoveSmallestSuffix(Dash, Some(word.clone())),
        RemoveSmallestSuffix(Dollar, Some(word.clone())),
        RemoveSmallestSuffix(Bang, Some(word.clone())),
        RemoveSmallestSuffix(Positional(0), Some(word.clone())),
        RemoveSmallestSuffix(Positional(10), Some(word.clone())),
        RemoveSmallestSuffix(Positional(100), Some(word.clone())),
        RemoveSmallestSuffix(Var(String::from("foo_bar123")), Some(word.clone())),

        RemoveSmallestSuffix(At, None),
        RemoveSmallestSuffix(Star, None),
        RemoveSmallestSuffix(Pound, None),
        RemoveSmallestSuffix(Question, None),
        RemoveSmallestSuffix(Dash, None),
        RemoveSmallestSuffix(Dollar, None),
        RemoveSmallestSuffix(Bang, None),
        RemoveSmallestSuffix(Positional(0), None),
        RemoveSmallestSuffix(Positional(10), None),
        RemoveSmallestSuffix(Positional(100), None),
        RemoveSmallestSuffix(Var(String::from("foo_bar123")), None),
    );

    let src = "${@%foo}${*%foo}${#%foo}${?%foo}${-%foo}${$%foo}${!%foo}${0%foo}${10%foo}${100%foo}${foo_bar123%foo}${@%}${*%}${#%}${?%}${-%}${$%}${!%}${0%}${10%}${100%}${foo_bar123%}";
    let mut p = make_parser(src);

    for s in substs {
        assert_eq!(word_subst(s), p.parameter().unwrap());
    }

    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_largest_suffix() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let word = word("foo");

    let substs = vec!(
        RemoveLargestSuffix(At, Some(word.clone())),
        RemoveLargestSuffix(Star, Some(word.clone())),
        RemoveLargestSuffix(Pound, Some(word.clone())),
        RemoveLargestSuffix(Question, Some(word.clone())),
        RemoveLargestSuffix(Dash, Some(word.clone())),
        RemoveLargestSuffix(Dollar, Some(word.clone())),
        RemoveLargestSuffix(Bang, Some(word.clone())),
        RemoveLargestSuffix(Positional(0), Some(word.clone())),
        RemoveLargestSuffix(Positional(10), Some(word.clone())),
        RemoveLargestSuffix(Positional(100), Some(word.clone())),
        RemoveLargestSuffix(Var(String::from("foo_bar123")), Some(word.clone())),

        RemoveLargestSuffix(At, None),
        RemoveLargestSuffix(Star, None),
        RemoveLargestSuffix(Pound, None),
        RemoveLargestSuffix(Question, None),
        RemoveLargestSuffix(Dash, None),
        RemoveLargestSuffix(Dollar, None),
        RemoveLargestSuffix(Bang, None),
        RemoveLargestSuffix(Positional(0), None),
        RemoveLargestSuffix(Positional(10), None),
        RemoveLargestSuffix(Positional(100), None),
        RemoveLargestSuffix(Var(String::from("foo_bar123")), None),
    );

    let src = "${@%%foo}${*%%foo}${#%%foo}${?%%foo}${-%%foo}${$%%foo}${!%%foo}${0%%foo}${10%%foo}${100%%foo}${foo_bar123%%foo}${@%%}${*%%}${#%%}${?%%}${-%%}${$%%}${!%%}${0%%}${10%%}${100%%}${foo_bar123%%}";
    let mut p = make_parser(src);

    for s in substs {
        assert_eq!(word_subst(s), p.parameter().unwrap());
    }

    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_smallest_prefix() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let word = word("foo");

    let substs = vec!(
        RemoveSmallestPrefix(At, Some(word.clone())),
        RemoveSmallestPrefix(Star, Some(word.clone())),
        RemoveSmallestPrefix(Pound, Some(word.clone())),
        RemoveSmallestPrefix(Question, Some(word.clone())),
        RemoveSmallestPrefix(Dash, Some(word.clone())),
        RemoveSmallestPrefix(Dollar, Some(word.clone())),
        RemoveSmallestPrefix(Bang, Some(word.clone())),
        RemoveSmallestPrefix(Positional(0), Some(word.clone())),
        RemoveSmallestPrefix(Positional(10), Some(word.clone())),
        RemoveSmallestPrefix(Positional(100), Some(word.clone())),
        RemoveSmallestPrefix(Var(String::from("foo_bar123")), Some(word.clone())),

        RemoveSmallestPrefix(At, None),
        RemoveSmallestPrefix(Star, None),
        //RemoveSmallestPrefix(Pound, None), // ${##} should parse as Len(#)
        RemoveSmallestPrefix(Question, None),
        RemoveSmallestPrefix(Dash, None),
        RemoveSmallestPrefix(Dollar, None),
        RemoveSmallestPrefix(Bang, None),
        RemoveSmallestPrefix(Positional(0), None),
        RemoveSmallestPrefix(Positional(10), None),
        RemoveSmallestPrefix(Positional(100), None),
        RemoveSmallestPrefix(Var(String::from("foo_bar123")), None),
    );

    let src = "${@#foo}${*#foo}${##foo}${?#foo}${-#foo}${$#foo}${!#foo}${0#foo}${10#foo}${100#foo}${foo_bar123#foo}${@#}${*#}${?#}${-#}${$#}${!#}${0#}${10#}${100#}${foo_bar123#}";
    let mut p = make_parser(src);

    for s in substs {
        assert_eq!(word_subst(s), p.parameter().unwrap());
    }

    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_largest_prefix() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let word = word("foo");

    let substs = vec!(
        RemoveLargestPrefix(At, Some(word.clone())),
        RemoveLargestPrefix(Star, Some(word.clone())),
        RemoveLargestPrefix(Pound, Some(word.clone())),
        RemoveLargestPrefix(Question, Some(word.clone())),
        RemoveLargestPrefix(Dash, Some(word.clone())),
        RemoveLargestPrefix(Dollar, Some(word.clone())),
        RemoveLargestPrefix(Bang, Some(word.clone())),
        RemoveLargestPrefix(Positional(0), Some(word.clone())),
        RemoveLargestPrefix(Positional(10), Some(word.clone())),
        RemoveLargestPrefix(Positional(100), Some(word.clone())),
        RemoveLargestPrefix(Var(String::from("foo_bar123")), Some(word.clone())),

        RemoveLargestPrefix(At, None),
        RemoveLargestPrefix(Star, None),
        RemoveLargestPrefix(Pound, None),
        RemoveLargestPrefix(Question, None),
        RemoveLargestPrefix(Dash, None),
        RemoveLargestPrefix(Dollar, None),
        RemoveLargestPrefix(Bang, None),
        RemoveLargestPrefix(Positional(0), None),
        RemoveLargestPrefix(Positional(10), None),
        RemoveLargestPrefix(Positional(100), None),
        RemoveLargestPrefix(Var(String::from("foo_bar123")), None),
    );

    let src = "${@##foo}${*##foo}${###foo}${?##foo}${-##foo}${$##foo}${!##foo}${0##foo}${10##foo}${100##foo}${foo_bar123##foo}${@##}${*##}${###}${?##}${-##}${$##}${!##}${0##}${10##}${100##}${foo_bar123##}";
    let mut p = make_parser(src);

    for s in substs {
        assert_eq!(word_subst(s), p.parameter().unwrap());
    }

    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_default() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let word = word("foo");

    let substs = vec!(
        Default(true, At, Some(word.clone())),
        Default(true, Star, Some(word.clone())),
        Default(true, Pound, Some(word.clone())),
        Default(true, Question, Some(word.clone())),
        Default(true, Dash, Some(word.clone())),
        Default(true, Dollar, Some(word.clone())),
        Default(true, Bang, Some(word.clone())),
        Default(true, Positional(0), Some(word.clone())),
        Default(true, Positional(10), Some(word.clone())),
        Default(true, Positional(100), Some(word.clone())),
        Default(true, Var(String::from("foo_bar123")), Some(word.clone())),

        Default(true, At, None),
        Default(true, Star, None),
        Default(true, Pound, None),
        Default(true, Question, None),
        Default(true, Dash, None),
        Default(true, Dollar, None),
        Default(true, Bang, None),
        Default(true, Positional(0), None),
        Default(true, Positional(10), None),
        Default(true, Positional(100), None),
        Default(true, Var(String::from("foo_bar123")), None),
    );

    let src = "${@:-foo}${*:-foo}${#:-foo}${?:-foo}${-:-foo}${$:-foo}${!:-foo}${0:-foo}${10:-foo}${100:-foo}${foo_bar123:-foo}${@:-}${*:-}${#:-}${?:-}${-:-}${$:-}${!:-}${0:-}${10:-}${100:-}${foo_bar123:-}";
    let mut p = make_parser(src);
    for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted

    let substs = vec!(
        Default(false, At, Some(word.clone())),
        Default(false, Star, Some(word.clone())),
        Default(false, Pound, Some(word.clone())),
        Default(false, Question, Some(word.clone())),
        Default(false, Dash, Some(word.clone())),
        Default(false, Dollar, Some(word.clone())),
        Default(false, Bang, Some(word.clone())),
        Default(false, Positional(0), Some(word.clone())),
        Default(false, Positional(10), Some(word.clone())),
        Default(false, Positional(100), Some(word.clone())),
        Default(false, Var(String::from("foo_bar123")), Some(word.clone())),

        Default(false, At, None),
        Default(false, Star, None),
        //Default(false, Pound, None), // ${#-} should be a length check of the `-` parameter
        Default(false, Question, None),
        Default(false, Dash, None),
        Default(false, Dollar, None),
        Default(false, Bang, None),
        Default(false, Positional(0), None),
        Default(false, Positional(10), None),
        Default(false, Positional(100), None),
        Default(false, Var(String::from("foo_bar123")), None),
    );

    let src = "${@-foo}${*-foo}${#-foo}${?-foo}${--foo}${$-foo}${!-foo}${0-foo}${10-foo}${100-foo}${foo_bar123-foo}${@-}${*-}${?-}${--}${$-}${!-}${0-}${10-}${100-}${foo_bar123-}";
    let mut p = make_parser(src);
    for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_error() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let word = word("foo");

    let substs = vec!(
        Error(true, At, Some(word.clone())),
        Error(true, Star, Some(word.clone())),
        Error(true, Pound, Some(word.clone())),
        Error(true, Question, Some(word.clone())),
        Error(true, Dash, Some(word.clone())),
        Error(true, Dollar, Some(word.clone())),
        Error(true, Bang, Some(word.clone())),
        Error(true, Positional(0), Some(word.clone())),
        Error(true, Positional(10), Some(word.clone())),
        Error(true, Positional(100), Some(word.clone())),
        Error(true, Var(String::from("foo_bar123")), Some(word.clone())),

        Error(true, At, None),
        Error(true, Star, None),
        Error(true, Pound, None),
        Error(true, Question, None),
        Error(true, Dash, None),
        Error(true, Dollar, None),
        Error(true, Bang, None),
        Error(true, Positional(0), None),
        Error(true, Positional(10), None),
        Error(true, Positional(100), None),
        Error(true, Var(String::from("foo_bar123")), None),
    );

    let src = "${@:?foo}${*:?foo}${#:?foo}${?:?foo}${-:?foo}${$:?foo}${!:?foo}${0:?foo}${10:?foo}${100:?foo}${foo_bar123:?foo}${@:?}${*:?}${#:?}${?:?}${-:?}${$:?}${!:?}${0:?}${10:?}${100:?}${foo_bar123:?}";
    let mut p = make_parser(src);
    for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted

    let substs = vec!(
        Error(false, At, Some(word.clone())),
        Error(false, Star, Some(word.clone())),
        Error(false, Pound, Some(word.clone())),
        Error(false, Question, Some(word.clone())),
        Error(false, Dash, Some(word.clone())),
        Error(false, Dollar, Some(word.clone())),
        Error(false, Bang, Some(word.clone())),
        Error(false, Positional(0), Some(word.clone())),
        Error(false, Positional(10), Some(word.clone())),
        Error(false, Positional(100), Some(word.clone())),
        Error(false, Var(String::from("foo_bar123")), Some(word.clone())),

        Error(false, At, None),
        Error(false, Star, None),
        //Error(false, Pound, None), // ${#?} should be a length check of the `?` parameter
        Error(false, Question, None),
        Error(false, Dash, None),
        Error(false, Dollar, None),
        Error(false, Bang, None),
        Error(false, Positional(0), None),
        Error(false, Positional(10), None),
        Error(false, Positional(100), None),
        Error(false, Var(String::from("foo_bar123")), None),
    );

    let src = "${@?foo}${*?foo}${#?foo}${??foo}${-?foo}${$?foo}${!?foo}${0?foo}${10?foo}${100?foo}${foo_bar123?foo}${@?}${*?}${??}${-?}${$?}${!?}${0?}${10?}${100?}${foo_bar123?}";
    let mut p = make_parser(src);
    for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_assign() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let word = word("foo");

    let substs = vec!(
        Assign(true, At, Some(word.clone())),
        Assign(true, Star, Some(word.clone())),
        Assign(true, Pound, Some(word.clone())),
        Assign(true, Question, Some(word.clone())),
        Assign(true, Dash, Some(word.clone())),
        Assign(true, Dollar, Some(word.clone())),
        Assign(true, Bang, Some(word.clone())),
        Assign(true, Positional(0), Some(word.clone())),
        Assign(true, Positional(10), Some(word.clone())),
        Assign(true, Positional(100), Some(word.clone())),
        Assign(true, Var(String::from("foo_bar123")), Some(word.clone())),

        Assign(true, At, None),
        Assign(true, Star, None),
        Assign(true, Pound, None),
        Assign(true, Question, None),
        Assign(true, Dash, None),
        Assign(true, Dollar, None),
        Assign(true, Bang, None),
        Assign(true, Positional(0), None),
        Assign(true, Positional(10), None),
        Assign(true, Positional(100), None),
        Assign(true, Var(String::from("foo_bar123")), None),
    );

    let src = "${@:=foo}${*:=foo}${#:=foo}${?:=foo}${-:=foo}${$:=foo}${!:=foo}${0:=foo}${10:=foo}${100:=foo}${foo_bar123:=foo}${@:=}${*:=}${#:=}${?:=}${-:=}${$:=}${!:=}${0:=}${10:=}${100:=}${foo_bar123:=}";
    let mut p = make_parser(src);
    for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted

    let substs = vec!(
        Assign(false, At, Some(word.clone())),
        Assign(false, Star, Some(word.clone())),
        Assign(false, Pound, Some(word.clone())),
        Assign(false, Question, Some(word.clone())),
        Assign(false, Dash, Some(word.clone())),
        Assign(false, Dollar, Some(word.clone())),
        Assign(false, Bang, Some(word.clone())),
        Assign(false, Positional(0), Some(word.clone())),
        Assign(false, Positional(10), Some(word.clone())),
        Assign(false, Positional(100), Some(word.clone())),
        Assign(false, Var(String::from("foo_bar123")), Some(word.clone())),

        Assign(false, At, None),
        Assign(false, Star, None),
        Assign(false, Pound, None),
        Assign(false, Question, None),
        Assign(false, Dash, None),
        Assign(false, Dollar, None),
        Assign(false, Bang, None),
        Assign(false, Positional(0), None),
        Assign(false, Positional(10), None),
        Assign(false, Positional(100), None),
        Assign(false, Var(String::from("foo_bar123")), None),
    );

    let src = "${@=foo}${*=foo}${#=foo}${?=foo}${-=foo}${$=foo}${!=foo}${0=foo}${10=foo}${100=foo}${foo_bar123=foo}${@=}${*=}${#=}${?=}${-=}${$=}${!=}${0=}${10=}${100=}${foo_bar123=}";
    let mut p = make_parser(src);
    for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_alternative() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let word = word("foo");

    let substs = vec!(
        Alternative(true, At, Some(word.clone())),
        Alternative(true, Star, Some(word.clone())),
        Alternative(true, Pound, Some(word.clone())),
        Alternative(true, Question, Some(word.clone())),
        Alternative(true, Dash, Some(word.clone())),
        Alternative(true, Dollar, Some(word.clone())),
        Alternative(true, Bang, Some(word.clone())),
        Alternative(true, Positional(0), Some(word.clone())),
        Alternative(true, Positional(10), Some(word.clone())),
        Alternative(true, Positional(100), Some(word.clone())),
        Alternative(true, Var(String::from("foo_bar123")), Some(word.clone())),

        Alternative(true, At, None),
        Alternative(true, Star, None),
        Alternative(true, Pound, None),
        Alternative(true, Question, None),
        Alternative(true, Dash, None),
        Alternative(true, Dollar, None),
        Alternative(true, Bang, None),
        Alternative(true, Positional(0), None),
        Alternative(true, Positional(10), None),
        Alternative(true, Positional(100), None),
        Alternative(true, Var(String::from("foo_bar123")), None),
    );

    let src = "${@:+foo}${*:+foo}${#:+foo}${?:+foo}${-:+foo}${$:+foo}${!:+foo}${0:+foo}${10:+foo}${100:+foo}${foo_bar123:+foo}${@:+}${*:+}${#:+}${?:+}${-:+}${$:+}${!:+}${0:+}${10:+}${100:+}${foo_bar123:+}";
    let mut p = make_parser(src);
    for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted

    let substs = vec!(
        Alternative(false, At, Some(word.clone())),
        Alternative(false, Star, Some(word.clone())),
        Alternative(false, Pound, Some(word.clone())),
        Alternative(false, Question, Some(word.clone())),
        Alternative(false, Dash, Some(word.clone())),
        Alternative(false, Dollar, Some(word.clone())),
        Alternative(false, Bang, Some(word.clone())),
        Alternative(false, Positional(0), Some(word.clone())),
        Alternative(false, Positional(10), Some(word.clone())),
        Alternative(false, Positional(100), Some(word.clone())),
        Alternative(false, Var(String::from("foo_bar123")), Some(word.clone())),

        Alternative(false, At, None),
        Alternative(false, Star, None),
        Alternative(false, Pound, None),
        Alternative(false, Question, None),
        Alternative(false, Dash, None),
        Alternative(false, Dollar, None),
        Alternative(false, Bang, None),
        Alternative(false, Positional(0), None),
        Alternative(false, Positional(10), None),
        Alternative(false, Positional(100), None),
        Alternative(false, Var(String::from("foo_bar123")), None),
    );

    let src = "${@+foo}${*+foo}${#+foo}${?+foo}${-+foo}${$+foo}${!+foo}${0+foo}${10+foo}${100+foo}${foo_bar123+foo}${@+}${*+}${#+}${?+}${-+}${$+}${!+}${0+}${10+}${100+}${foo_bar123+}";
    let mut p = make_parser(src);
    for s in substs { assert_eq!(word_subst(s), p.parameter().unwrap()); }
    assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
}

#[test]
fn test_parameter_substitution_words_can_have_spaces_and_escaped_curlies() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let var = Var(String::from("foo_bar123"));
    let word = TopLevelWord(Concat(vec!(
        lit("foo{"),
        escaped("}"),
        lit(" \t\r "),
        escaped("\n"),
        lit("bar \t\r "),
    )));

    let substs = vec!(
        RemoveSmallestSuffix(var.clone(), Some(word.clone())),
        RemoveLargestSuffix(var.clone(), Some(word.clone())),
        RemoveSmallestPrefix(var.clone(), Some(word.clone())),
        RemoveLargestPrefix(var.clone(), Some(word.clone())),
        Default(true, var.clone(), Some(word.clone())),
        Default(false, var.clone(), Some(word.clone())),
        Assign(true, var.clone(), Some(word.clone())),
        Assign(false, var.clone(), Some(word.clone())),
        Error(true, var.clone(), Some(word.clone())),
        Error(false, var.clone(), Some(word.clone())),
        Alternative(true, var.clone(), Some(word.clone())),
        Alternative(false, var.clone(), Some(word.clone())),
    );

    let src = vec!(
        "%",
        "%%",
        "#",
        "##",
        ":-",
        "-",
        ":=",
        "=",
        ":?",
        "?",
        ":+",
        "+",
    );

    for (i, s) in substs.into_iter().enumerate() {
        let src = format!("${{foo_bar123{}foo{{\\}} \t\r \\\nbar \t\r }}", src[i]);
        let mut p = make_parser(&src);
        assert_eq!(word_subst(s), p.parameter().unwrap());
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }
}

#[test]
fn test_parameter_substitution_words_can_start_with_pound() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let var = Var(String::from("foo_bar123"));
    let word = TopLevelWord(Concat(vec!(
        lit("#foo{"),
        escaped("}"),
        lit(" \t\r "),
        escaped("\n"),
        lit("bar \t\r "),
    )));

    let substs = vec!(
        RemoveSmallestSuffix(var.clone(), Some(word.clone())),
        RemoveLargestSuffix(var.clone(), Some(word.clone())),
        //RemoveSmallestPrefix(var.clone(), Some(word.clone())),
        RemoveLargestPrefix(var.clone(), Some(word.clone())),
        Default(true, var.clone(), Some(word.clone())),
        Default(false, var.clone(), Some(word.clone())),
        Assign(true, var.clone(), Some(word.clone())),
        Assign(false, var.clone(), Some(word.clone())),
        Error(true, var.clone(), Some(word.clone())),
        Error(false, var.clone(), Some(word.clone())),
        Alternative(true, var.clone(), Some(word.clone())),
        Alternative(false, var.clone(), Some(word.clone())),
    );

    let src = vec!(
        "%",
        "%%",
        //"#", // Let's not confuse the pound in the word with a substitution
        "##",
        ":-",
        "-",
        ":=",
        "=",
        ":?",
        "?",
        ":+",
        "+",
    );

    for (i, s) in substs.into_iter().enumerate() {
        let src = format!("${{foo_bar123{}#foo{{\\}} \t\r \\\nbar \t\r }}", src[i]);
        let mut p = make_parser(&src);
        assert_eq!(word_subst(s), p.parameter().unwrap());
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }
}

#[test]
fn test_parameter_substitution_words_can_be_parameters_or_substitutions_as_well() {
    use shell_lang::ast::Parameter::*;
    use shell_lang::ast::ParameterSubstitution::*;

    let var = Var(String::from("foo_bar123"));
    let word = TopLevelWord(Concat(vec!(
        Word::Simple(Param(At)),
        subst(RemoveLargestPrefix(
            Var(String::from("foo")),
            Some(word("bar"))
        )),
    )));

    let substs = vec!(
        RemoveSmallestSuffix(var.clone(), Some(word.clone())),
        RemoveLargestSuffix(var.clone(), Some(word.clone())),
        RemoveSmallestPrefix(var.clone(), Some(word.clone())),
        RemoveLargestPrefix(var.clone(), Some(word.clone())),
        Default(true, var.clone(), Some(word.clone())),
        Default(false, var.clone(), Some(word.clone())),
        Assign(true, var.clone(), Some(word.clone())),
        Assign(false, var.clone(), Some(word.clone())),
        Error(true, var.clone(), Some(word.clone())),
        Error(false, var.clone(), Some(word.clone())),
        Alternative(true, var.clone(), Some(word.clone())),
        Alternative(false, var.clone(), Some(word.clone())),
    );

    let src = vec!(
        "%",
        "%%",
        "#",
        "##",
        ":-",
        "-",
        ":=",
        "=",
        ":?",
        "?",
        ":+",
        "+",
    );

    for (i, s) in substs.into_iter().enumerate() {
        let src = format!("${{foo_bar123{}$@${{foo##bar}}}}", src[i]);
        let mut p = make_parser(&src);
        assert_eq!(word_subst(s), p.parameter().unwrap());
        assert_eq!(Err(UnexpectedEOF), p.parameter()); // Stream should be exhausted
    }
}

#[test]
fn test_parameter_substitution_command_close_paren_need_not_be_followed_by_word_delimeter() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(), io: vec!(),
        cmd: Some((word("foo"), vec!(TopLevelWord(Single(Word::DoubleQuoted(vec!(
            Subst(Box::new(ParameterSubstitution::Command(vec!(cmd("bar")))))
        ))))))),
    }));
    assert_eq!(correct, make_parser("foo \"$(bar)\"").complete_command().unwrap());
}

#[test]
fn test_parameter_substitution_invalid() {
    let cases = vec!(
        ("$(( x",     UnexpectedEOF),
        ("${foo",     UnexpectedEOF),
        ("${ foo}",   BadSubst(Token::Whitespace(String::from(" ")), src(2,1,3))),
        ("${foo }",   BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo -}",  BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo =}",  BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo ?}",  BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo +}",  BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo :-}", BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo :=}", BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo :?}", BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo :+}", BadSubst(Token::Whitespace(String::from(" ")), src(5,1,6))),
        ("${foo: -}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
        ("${foo: =}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
        ("${foo: ?}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
        ("${foo: +}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
        ("${foo: %}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
        ("${foo: #}", BadSubst(Token::Whitespace(String::from(" ")), src(6,1,7))),
        ("${'foo'}",  BadSubst(Token::SingleQuote, src(2,1,3))),
        ("${\"foo\"}", BadSubst(Token::DoubleQuote, src(2,1,3))),
        ("${`foo`}",  BadSubst(Token::Backtick, src(2,1,3))),
    );

    for (s, correct) in cases.into_iter() {
        match make_parser(s).parameter() {
            Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
            Err(ref err) => if err != &correct {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       s, correct, err);
            },
        }
    }
}

#[test]
fn test_redirect_valid_close_without_whitespace() {
    let mut p = make_parser(">&-");
    assert_eq!(Some(Ok(Redirect::DupWrite(None, word("-")))), p.redirect().unwrap());
}

#[test]
fn test_redirect_valid_close_with_whitespace() {
    let mut p = make_parser("<&       -");
    assert_eq!(Some(Ok(Redirect::DupRead(None, word("-")))), p.redirect().unwrap());
}

#[test]
fn test_redirect_valid_start_with_dash_if_not_dup() {
    let path = word("-test");
    let cases = vec!(
        ("4<-test",  Redirect::Read(Some(4), path.clone())),
        ("4>-test",  Redirect::Write(Some(4), path.clone())),
        ("4<>-test", Redirect::ReadWrite(Some(4), path.clone())),
        ("4>>-test", Redirect::Append(Some(4), path.clone())),
        ("4>|-test", Redirect::Clobber(Some(4), path.clone())),
    );

    for (s, correct) in cases.into_iter() {
        match make_parser(s).redirect() {
            Ok(Some(Ok(ref r))) if *r == correct => {},
            Ok(r) => {
                panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", s, r, correct)
            },
            Err(err) => panic!("Failed to parse the source \"{}\": {}", s, err),
        }
    }
}

#[test]
fn test_redirect_valid_return_word_if_no_redirect() {
    let mut p = make_parser("hello");
    assert_eq!(Some(Err(word("hello"))), p.redirect().unwrap());
}

#[test]
fn test_redirect_valid_return_word_if_src_fd_is_definitely_non_numeric() {
    let mut p = make_parser("123$$'foo'>out");
    let correct = TopLevelWord(Concat(vec!(
        lit("123"),
        Word::Simple(Param(Parameter::Dollar)),
        Word::SingleQuoted(String::from("foo")),
    )));
    assert_eq!(Some(Err(correct)), p.redirect().unwrap());
}

#[test]
fn test_redirect_valid_return_word_if_src_fd_has_escaped_numerics() {
    let mut p = make_parser("\\2>");
    let correct = word_escaped("2");
    assert_eq!(Some(Err(correct)), p.redirect().unwrap());
}

#[test]
fn test_redirect_valid_dst_fd_can_have_escaped_numerics() {
    let mut p = make_parser(">\\2");
    let correct = Redirect::Write(None, word_escaped("2"));
    assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
}

#[test]
fn test_redirect_invalid_dup_if_dst_fd_is_definitely_non_numeric() {
    assert_eq!(Err(BadFd(src(2, 1, 3), src(12, 1, 13))), make_parser(">&123$$'foo'").redirect());
}

#[test]
fn test_redirect_valid_dup_return_redirect_if_dst_fd_is_possibly_numeric() {
    let mut p = make_parser(">&123$$$(echo 2)`echo bar`");
    let correct = Redirect::DupWrite(
        None,
        TopLevelWord(Concat(vec!(
            lit("123"),
            Word::Simple(Param(Parameter::Dollar)),
            subst(ParameterSubstitution::Command(vec!(cmd_args("echo", &["2"])))),
            subst(ParameterSubstitution::Command(vec!(cmd_args("echo", &["bar"])))),
        ))),
    );
    assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
}

#[test]
fn test_redirect_invalid_close_without_whitespace() {
    assert_eq!(Err(BadFd(src(2, 1, 3), src(7, 1, 8))), make_parser(">&-asdf").redirect());
}

#[test]
fn test_redirect_invalid_close_with_whitespace() {
    assert_eq!(Err(BadFd(src(9, 1, 10), src(14, 1, 15))), make_parser("<&       -asdf").redirect());
}

#[test]
fn test_redirect_fd_immediately_preceeding_redirection() {
    let mut p = make_parser("foo 1>>out");
    let cmd = p.simple_command().unwrap();
    assert_eq!(cmd, Simple(Box::new(SimpleCommand {
        cmd: Some((word("foo"), vec!())),
        vars: vec!(),
        io: vec!(Redirect::Append(Some(1), word("out"))),
    })));
}

#[test]
fn test_redirect_fd_must_immediately_preceed_redirection() {
    let mut p = make_parser("foo 1 <>out");
    let cmd = p.simple_command().unwrap();
    assert_eq!(cmd, Simple(Box::new(SimpleCommand {
        cmd: Some((word("foo"), vec!(word("1")))),
        vars: vec!(),
        io: vec!(Redirect::ReadWrite(None, word("out"))),
    })));
}

#[test]
fn test_redirect_valid_dup_with_fd() {
    let mut p = make_parser("foo 1>&2");
    let cmd = p.simple_command().unwrap();
    assert_eq!(cmd, Simple(Box::new(SimpleCommand {
        cmd: Some((word("foo"), vec!())),
        vars: vec!(),
        io: vec!(Redirect::DupWrite(Some(1), word("2"))),
    })));
}

#[test]
fn test_redirect_valid_dup_without_fd() {
    let mut p = make_parser("foo 1 <&2");
    let cmd = p.simple_command().unwrap();
    assert_eq!(cmd, Simple(Box::new(SimpleCommand {
        cmd: Some((word("foo"), vec!(word("1")))),
        vars: vec!(),
        io: vec!(Redirect::DupRead(None, word("2"))),
    })));
}

#[test]
fn test_redirect_valid_dup_with_whitespace() {
    let mut p = make_parser("foo 1<& 2");
    let cmd = p.simple_command().unwrap();
    assert_eq!(cmd, Simple(Box::new(SimpleCommand {
        cmd: Some((word("foo"), vec!())),
        vars: vec!(),
        io: vec!(Redirect::DupRead(Some(1), word("2"))),
    })));
}

#[test]
fn test_redirect_valid_single_quoted_dup_fd() {
    let correct = Redirect::DupWrite(Some(1), single_quoted("2"));
    assert_eq!(Some(Ok(correct)), make_parser("1>&'2'").redirect().unwrap());
}

#[test]
fn test_redirect_valid_double_quoted_dup_fd() {
    let correct = Redirect::DupWrite(None, double_quoted("2"));
    assert_eq!(Some(Ok(correct)), make_parser(">&\"2\"").redirect().unwrap());
}

#[test]
fn test_redirect_src_fd_need_not_be_single_token() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("foo")),
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("12")),
        Token::Literal(String::from("34")),
        Token::LessAnd,
        Token::Dash,
    ));

    let cmd = p.simple_command().unwrap();
    assert_eq!(cmd, Simple(Box::new(SimpleCommand {
        cmd: Some((word("foo"), vec!())),
        vars: vec!(),
        io: vec!(Redirect::DupRead(Some(1234), word("-"))),
    })));
}

#[test]
fn test_redirect_dst_fd_need_not_be_single_token() {
    let mut p = make_parser_from_tokens(vec!(
        Token::GreatAnd,
        Token::Literal(String::from("12")),
        Token::Literal(String::from("34")),
    ));

    let correct = Redirect::DupWrite(None, word("1234"));
    assert_eq!(Some(Ok(correct)), p.redirect().unwrap());
}

#[test]
fn test_redirect_accept_literal_and_name_tokens() {
    let mut p = make_parser_from_tokens(vec!(
        Token::GreatAnd,
        Token::Literal(String::from("12")),
    ));
    assert_eq!(Some(Ok(Redirect::DupWrite(None, word("12")))), p.redirect().unwrap());

    let mut p = make_parser_from_tokens(vec!(
        Token::GreatAnd,
        Token::Name(String::from("12")),
    ));
    assert_eq!(Some(Ok(Redirect::DupWrite(None, word("12")))), p.redirect().unwrap());
}

#[test]
fn test_simple_command_valid_assignments_at_start_of_command() {
    let mut p = make_parser("var=val ENV=true BLANK= foo bar baz");
    let SimpleCommandFragments { cmd, vars, ..} = sample_simple_command();
    let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: vec!() }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_simple_command_assignments_after_start_of_command_should_be_args() {
    let mut p = make_parser("var=val ENV=true BLANK= foo var2=val2 bar baz var3=val3");
    let SimpleCommandFragments { cmd, vars, ..} = sample_simple_command();
    let (cmd, mut args) = cmd.unwrap();
    args.insert(0, word("var2=val2"));
    args.push(word("var3=val3"));
    let correct = Simple(Box::new(SimpleCommand { cmd: Some((cmd, args)), vars: vars, io: vec!() }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_simple_command_redirections_at_start_of_command() {
    let mut p = make_parser("2>|clob 3<>rw <in var=val ENV=true BLANK= foo bar baz");
    let SimpleCommandFragments { cmd, vars, io } = sample_simple_command();
    let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_simple_command_redirections_at_end_of_command() {
    let mut p = make_parser("var=val ENV=true BLANK= foo bar baz 2>|clob 3<>rw <in");
    let SimpleCommandFragments { cmd, vars, io } = sample_simple_command();
    let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_simple_command_redirections_throughout_the_command() {
    let mut p = make_parser("2>|clob var=val 3<>rw ENV=true BLANK= foo bar <in baz 4>&-");
    let SimpleCommandFragments { cmd, vars, mut io } = sample_simple_command();
    io.push(Redirect::DupWrite(Some(4), word("-")));
    let correct = Simple(Box::new(SimpleCommand { cmd: cmd, vars: vars, io: io }));
    assert_eq!(correct, p.simple_command().unwrap());
}

#[test]
fn test_heredoc_valid() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<eof\nhello\neof\n").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_eof_after_delimiter_allowed() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<eof\nhello\neof").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_with_empty_body() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word(""))),
    }));

    assert_eq!(correct, make_parser("cat <<eof\neof").complete_command().unwrap());
    assert_eq!(correct, make_parser("cat <<eof\n").complete_command().unwrap());
    assert_eq!(correct, make_parser("cat <<eof").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_eof_acceptable_as_delimeter() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<eof\nhello\neof").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_does_not_lose_tokens_up_to_next_newline() {
    let mut p = make_parser("cat <<eof1; cat 3<<eof2\nhello\neof1\nworld\neof2");
    let cat = Some((word("cat"), vec!()));
    let first = Some(cmd_from_simple(SimpleCommand {
        cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));
    let second = Some(cmd_from_simple(SimpleCommand {
        cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(Some(3), word("world\n")))
    }));

    assert_eq!(first, p.complete_command().unwrap());
    assert_eq!(second, p.complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_space_before_delimeter_allowed() {
    let mut p = make_parser("cat <<   eof1; cat 3<<- eof2\nhello\neof1\nworld\neof2");
    let cat = Some((word("cat"), vec!()));
    let first = Some(cmd_from_simple(SimpleCommand {
        cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));
    let second = Some(cmd_from_simple(SimpleCommand {
        cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(Some(3), word("world\n")))
    }));

    assert_eq!(first, p.complete_command().unwrap());
    assert_eq!(second, p.complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_unquoted_delimeter_should_expand_body() {
    let cat = Some((word("cat"), vec!()));
    let expanded = Some(cmd_from_simple(SimpleCommand {
        cmd: cat.clone(), vars: vec!(), io: vec!(
            Redirect::Heredoc(None, TopLevelWord(Concat(vec!(
                Word::Simple(Param(Parameter::Dollar)),
                lit(" "),
                subst(ParameterSubstitution::Len(Parameter::Bang)),
                lit(" "),
                subst(ParameterSubstitution::Command(vec!(cmd("foo")))),
                lit("\n"),
            )))
        ))
    }));
    let literal = Some(cmd_from_simple(SimpleCommand {
        cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(None, word("$$ ${#!} `foo`\n")))
    }));

    assert_eq!(expanded, make_parser("cat <<eof\n$$ ${#!} `foo`\neof").complete_command().unwrap());
    assert_eq!(literal, make_parser("cat <<'eof'\n$$ ${#!} `foo`\neof").complete_command().unwrap());
    assert_eq!(literal, make_parser("cat <<`eof`\n$$ ${#!} `foo`\n`eof`").complete_command().unwrap());
    assert_eq!(literal, make_parser("cat <<\"eof\"\n$$ ${#!} `foo`\neof").complete_command().unwrap());
    assert_eq!(literal, make_parser("cat <<e\\of\n$$ ${#!} `foo`\neof").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_leading_tab_removal_works() {
    let mut p = make_parser("cat <<-eof1; cat 3<<-eof2\n\t\thello\n\teof1\n\t\t \t\nworld\n\t\teof2");
    let cat = Some((word("cat"), vec!()));
    let first = Some(cmd_from_simple(SimpleCommand {
        cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));
    let second = Some(cmd_from_simple(SimpleCommand {
        cmd: cat.clone(), vars: vec!(), io: vec!(Redirect::Heredoc(Some(3), word(" \t\nworld\n")))
    }));

    assert_eq!(first, p.complete_command().unwrap());
    assert_eq!(second, p.complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_leading_tab_removal_works_if_dash_immediately_after_dless() {
    let mut p = make_parser("cat 3<< -eof\n\t\t \t\nworld\n\t\teof\n\t\t-eof\n-eof");
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(Some(3), word("\t\t \t\nworld\n\t\teof\n\t\t-eof\n")))
    }));

    assert_eq!(correct, p.complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_unquoted_backslashes_in_delimeter_disappear() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<e\\ f\\f\nhello\ne ff").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_balanced_single_quotes_in_delimeter() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<e'o'f\nhello\neof").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_balanced_double_quotes_in_delimeter() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<e\"\\o${foo}\"f\nhello\ne\\o${foo}f").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_balanced_backticks_in_delimeter() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<e`\\o\\$\\`\\\\${f}`\nhello\ne`\\o$`\\${f}`").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_balanced_parens_in_delimeter() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<eof(  )\nhello\neof(  )").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_cmd_subst_in_delimeter() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));

    assert_eq!(correct, make_parser("cat <<eof$(  )\nhello\neof$(  )").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_param_subst_in_delimeter() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\n")))
    }));
    assert_eq!(correct, make_parser("cat <<eof${  }\nhello\neof${  }").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_skip_past_newlines_in_single_quotes() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!(
            single_quoted("\n"), word("arg")
        ))),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF '\n' arg\nhere\nEOF").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_skip_past_newlines_in_double_quotes() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!(
            double_quoted("\n"),
            word("arg")
        ))),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF \"\n\" arg\nhere\nEOF").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_skip_past_newlines_in_backticks() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!(
            word_subst(ParameterSubstitution::Command(vec!(cmd("echo")))),
            word("arg")
        ))),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF `echo \n` arg\nhere\nEOF").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_skip_past_newlines_in_parens() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF; (foo\n); arg\nhere\nEOF").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_skip_past_newlines_in_cmd_subst() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!(
            word_subst(ParameterSubstitution::Command(vec!(cmd("foo")))),
            word("arg"),
        ))),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF $(foo\n) arg\nhere\nEOF").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_skip_past_newlines_in_param_subst() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!(
            word_subst(ParameterSubstitution::Assign(
                    false,
                    Parameter::Var(String::from("foo")),
                    Some(word("\n"))
            )),
            word("arg")
        ))),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF ${foo=\n} arg\nhere\nEOF").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_skip_past_escaped_newlines() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!(word("arg")))),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF \\\n arg\nhere\nEOF").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_double_quoted_delim_keeps_backslashe_except_after_specials() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<\"\\EOF\\$\\`\\\"\\\\\"\nhere\n\\EOF$`\"\\\n")
               .complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_unquoting_only_removes_outer_quotes_and_backslashes() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF${ 'asdf'}(\"hello'\"){\\o}\nhere\nEOF${ asdf}(hello'){o}")
               .complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_delimeter_can_be_followed_by_carriage_return_newline() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!(word("arg")))),
        io: vec!(Redirect::Heredoc(None, word("here\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF arg\nhere\nEOF\r\n").complete_command().unwrap());

    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!(word("arg")))),
        io: vec!(Redirect::Heredoc(None, word("here\r\n")))
    }));
    assert_eq!(correct, make_parser("cat <<EOF arg\nhere\r\nEOF\r\n").complete_command().unwrap());
}

#[test]
fn test_heredoc_valid_delimiter_can_start_with() {
    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("\thello\n\t\tworld\n")))
    }));
    assert_eq!(correct, make_parser("cat << -EOF\n\thello\n\t\tworld\n-EOF").complete_command().unwrap());

    let correct = Some(cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("cat"), vec!())),
        io: vec!(Redirect::Heredoc(None, word("hello\nworld\n")))
    }));
    assert_eq!(correct, make_parser("cat <<--EOF\n\thello\n\t\tworld\n-EOF").complete_command().unwrap());
}

#[test]
fn test_heredoc_invalid_missing_delimeter() {
    assert_eq!(Err(Unexpected(Token::Semi, src(7, 1, 8))), make_parser("cat << ;").complete_command());
}

#[test]
fn test_heredoc_invalid_unbalanced_quoting() {
    assert_eq!(Err(Unmatched(Token::SingleQuote, src(6,  1,  7))), make_parser("cat <<'eof" ).complete_command());
    assert_eq!(Err(Unmatched(Token::Backtick,    src(6,  1,  7))), make_parser("cat <<`eof" ).complete_command());
    assert_eq!(Err(Unmatched(Token::DoubleQuote, src(6,  1,  7))), make_parser("cat <<\"eof").complete_command());
    assert_eq!(Err(Unmatched(Token::ParenOpen,   src(9,  1, 10))), make_parser("cat <<eof(" ).complete_command());
    assert_eq!(Err(Unmatched(Token::ParenOpen,   src(10, 1, 11))), make_parser("cat <<eof$(").complete_command());
    assert_eq!(Err(Unmatched(Token::CurlyOpen,   src(10, 1, 11))), make_parser("cat <<eof${").complete_command());
}

#[test]
fn test_heredoc_invalid_shows_right_position_of_error() {
    let mut p = make_parser("cat <<EOF\nhello\n${invalid subst\nEOF");
    assert_eq!(
        Err(BadSubst(Token::Whitespace(String::from(" ")), src(25,3,10))),
        p.complete_command()
    );
}

#[test]
fn test_heredoc_invalid_shows_right_position_of_error_when_tabs_stripped() {
    let mut p = make_parser("cat <<-EOF\n\t\thello\n\t\t${invalid subst\n\t\t\tEOF");
    assert_eq!(
        Err(BadSubst(Token::Whitespace(String::from(" ")), src(30,3,12))),
        p.complete_command()
    );
}

#[test]
fn test_heredoc_keeps_track_of_correct_position_after_redirect() {
    let mut p = make_parser("cat <<EOF arg ()\nhello\nEOF");
    // Grab the heredoc command
    p.complete_command().unwrap();
    // Fail on the ()
    assert_eq!(Err(Unexpected(Token::ParenClose, src(15,1,16))), p.complete_command());
}

#[test]
fn test_redirect_list_valid() {
    let mut p = make_parser("1>>out <& 2 2>&-");
    let io = p.redirect_list().unwrap();
    assert_eq!(io, vec!(
        Redirect::Append(Some(1), word("out")),
        Redirect::DupRead(None, word("2")),
        Redirect::DupWrite(Some(2), word("-")),
    ));
}

#[test]
fn test_redirect_list_rejects_non_fd_words() {
    assert_eq!(Err(BadFd(src(16, 1, 17), src(19, 1, 20))), make_parser("1>>out <in 2>&- abc").redirect_list());
    assert_eq!(Err(BadFd(src(7,  1, 8),  src(10,  1, 11))), make_parser("1>>out abc<in 2>&-").redirect_list());
    assert_eq!(Err(BadFd(src(7,  1, 8),  src(10,  1, 11))), make_parser("1>>out abc <in 2>&-").redirect_list());
}

#[test]
fn test_do_group_valid() {
    let mut p = make_parser("do foo\nbar; baz; done");
    let correct = vec!(cmd("foo"), cmd("bar"), cmd("baz"));
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
    let correct = vec!(cmd_args("foo", &["done"]));
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
    assert_eq!(Err(IncompleteCmd("do", src(0,1,1), "done", src(7,2,5))), p.do_group());
}

#[test]
fn test_brace_group_valid() {
    let mut p = make_parser("{ foo\nbar; baz; }");
    let correct = vec!(cmd("foo"), cmd("bar"), cmd("baz"));
    assert_eq!(correct, p.brace_group().unwrap());
}

#[test]
fn test_brace_group_invalid_missing_separator() {
    assert_eq!(Err(Unmatched(Token::CurlyOpen, src(0,1,1))), make_parser("{ foo\nbar; baz }").brace_group());
}

#[test]
fn test_brace_group_invalid_start_must_be_whitespace_delimited() {
    let mut p = make_parser("{foo\nbar; baz; }");
    assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(1,1,2))), p.brace_group());
}

#[test]
fn test_brace_group_valid_end_must_be_whitespace_and_separator_delimited() {
    let mut p = make_parser("{ foo\nbar}; baz; }");
    p.brace_group().unwrap();
    assert_eq!(p.complete_command().unwrap(), None); // Ensure stream is empty
    let mut p = make_parser("{ foo\nbar; }baz; }");
    p.brace_group().unwrap();
    assert_eq!(p.complete_command().unwrap(), None); // Ensure stream is empty
}

#[test]
fn test_brace_group_valid_keyword_delimited_by_separator() {
    let mut p = make_parser("{ foo }; }");
    let correct = vec!(cmd_args("foo", &["}"]));
    assert_eq!(correct, p.brace_group().unwrap());
}

#[test]
fn test_brace_group_invalid_missing_keyword() {
    let mut p = make_parser("{ foo\nbar; baz");
    assert_eq!(Err(Unmatched(Token::CurlyOpen, src(0,1,1))), p.brace_group());
    let mut p = make_parser("foo\nbar; baz; }");
    assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(0,1,1))), p.brace_group());
}

#[test]
fn test_brace_group_invalid_quoted() {
    let cmds = [
        ("'{' foo\nbar; baz; }",   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("{ foo\nbar; baz; '}'",   Unmatched(Token::CurlyOpen, src(0,1,1))),
        ("\"{\" foo\nbar; baz; }", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("{ foo\nbar; baz; \"}\"", Unmatched(Token::CurlyOpen, src(0,1,1))),
    ];

    for &(c, ref e) in cmds.into_iter() {
        match make_parser(c).brace_group() {
            Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       c, e, err);
            }
        }
    }
}

#[test]
fn test_brace_group_invalid_missing_body() {
    assert_eq!(Err(Unmatched(Token::CurlyOpen, src(0, 1, 1))), make_parser("{\n}").brace_group());
}

#[test]
fn test_subshell_valid() {
    let mut p = make_parser("( foo\nbar; baz; )");
    let correct = vec!(cmd("foo"), cmd("bar"), cmd("baz"));
    assert_eq!(correct, p.subshell().unwrap());
}

#[test]
fn test_subshell_valid_separator_not_needed() {
    let mut p = make_parser("( foo )");
    let correct = vec!(cmd("foo"));
    assert_eq!(correct, p.subshell().unwrap());
}

#[test]
fn test_subshell_space_between_parens_not_needed() {
    let mut p = make_parser("(foo )");
    p.subshell().unwrap();
    let mut p = make_parser("( foo)");
    p.subshell().unwrap();
    let mut p = make_parser("(foo)");
    p.subshell().unwrap();
}

#[test]
fn test_subshell_invalid_missing_keyword() {
    assert_eq!(Err(Unmatched(Token::ParenOpen, src(0,1,1))), make_parser("( foo\nbar; baz").subshell());
    assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(0,1,1))),
        make_parser("foo\nbar; baz; )").subshell());
}

#[test]
fn test_subshell_invalid_quoted() {
    let cmds = [
        ("'(' foo\nbar; baz; )",   Unexpected(Token::SingleQuote, src(0,1,1))),
        ("( foo\nbar; baz; ')'",   Unmatched(Token::ParenOpen, src(0,1,1))),
        ("\"(\" foo\nbar; baz; )", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("( foo\nbar; baz; \")\"", Unmatched(Token::ParenOpen, src(0,1,1))),
    ];

    for &(c, ref e) in cmds.into_iter() {
        match make_parser(c).subshell() {
            Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       c, e, err);
            },
        }
    }
}

#[test]
fn test_subshell_invalid_missing_body() {
    assert_eq!(Err(Unexpected(Token::ParenClose, src(2,2,1))), make_parser("(\n)").subshell());
    assert_eq!(Err(Unexpected(Token::ParenClose, src(1,1,2))), make_parser("()").subshell());
}

#[test]
fn test_loop_command_while_valid() {
    let mut p = make_parser("while guard1; guard2; do foo\nbar; baz; done");
    let (until, GuardBodyPair { guard, body }) = p.loop_command().unwrap();

    let correct_guard = vec!(cmd("guard1"), cmd("guard2"));
    let correct_body = vec!(cmd("foo"), cmd("bar"), cmd("baz"));

    assert_eq!(until, builder::LoopKind::While);
    assert_eq!(correct_guard, guard);
    assert_eq!(correct_body, body);
}

#[test]
fn test_loop_command_until_valid() {
    let mut p = make_parser("until guard1\n guard2\n do foo\nbar; baz; done");
    let (until, GuardBodyPair { guard, body }) = p.loop_command().unwrap();

    let correct_guard = vec!(cmd("guard1"), cmd("guard2"));
    let correct_body = vec!(cmd("foo"), cmd("bar"), cmd("baz"));

    assert_eq!(until, builder::LoopKind::Until);
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
fn test_if_command_valid_with_else() {
    let guard1 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("guard1"), vec!())),
        io: vec!(Redirect::Read(None, word("in"))),
    });

    let guard2 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("guard2"), vec!())),
        io: vec!(Redirect::Write(None, word("out"))),
    });

    let guard3 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("guard3"), vec!())),
        io: vec!(),
    });

    let body1 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("body1"), vec!())),
        io: vec!(Redirect::Clobber(None, word("clob"))),
    });

    let body2 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("body2"), vec!())),
        io: vec!(Redirect::Append(Some(2), word("app"))),
    });

    let els = cmd("else");

    let correct = builder::IfFragments {
        conditionals: vec!(
            GuardBodyPair { guard: vec!(guard1, guard2), body: vec!(body1) },
            GuardBodyPair { guard: vec!(guard3), body: vec!(body2) },
        ),
        else_branch: Some(vec!(els)),
    };
    let mut p = make_parser("if guard1 <in; >out guard2; then body1 >|clob\n elif guard3; then body2 2>>app; else else; fi");
    assert_eq!(correct, p.if_command().unwrap());
}

#[test]
fn test_if_command_valid_without_else() {
    let guard1 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("guard1"), vec!())),
        io: vec!(Redirect::Read(None, word("in"))),
    });

    let guard2 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("guard2"), vec!())),
        io: vec!(Redirect::Write(None, word("out"))),
    });

    let guard3 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("guard3"), vec!())),
        io: vec!(),
    });

    let body1 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("body1"), vec!())),
        io: vec!(Redirect::Clobber(None, word("clob"))),
    });

    let body2 = cmd_from_simple(SimpleCommand {
        vars: vec!(),
        cmd: Some((word("body2"), vec!())),
        io: vec!(Redirect::Append(Some(2), word("app"))),
    });

    let correct = builder::IfFragments {
        conditionals: vec!(
            GuardBodyPair { guard: vec!(guard1, guard2), body: vec!(body1) },
            GuardBodyPair { guard: vec!(guard3), body: vec!(body2) },
        ),
        else_branch: None,
    };
    let mut p = make_parser("if guard1 <in; >out guard2; then body1 >|clob\n elif guard3; then body2 2>>app; fi");
    assert_eq!(correct, p.if_command().unwrap());
}

#[test]
fn test_if_command_invalid_missing_separator() {
    let mut p = make_parser("if guard; then body1; elif guard2; then body2; else else fi");
    assert_eq!(Err(IncompleteCmd("if", src(0,1,1), "fi", src(59,1,60))), p.if_command());
}

#[test]
fn test_if_command_invalid_missing_keyword() {
    let mut p = make_parser("guard1; then body1; elif guard2; then body2; else else; fi");
    assert_eq!(Err(Unexpected(Token::Name(String::from("guard1")), src(0,1,1))), p.if_command());
    let mut p = make_parser("if guard1; then body1; elif guard2; then body2; else else;");
    assert_eq!(Err(IncompleteCmd("if", src(0,1,1), "fi", src(58,1,59))), p.if_command());
}

#[test]
fn test_if_command_invalid_missing_guard() {
    let mut p = make_parser("if; then body1; elif guard2; then body2; else else; fi");
    assert_eq!(Err(Unexpected(Token::Semi, src(2,1,3))), p.if_command());
}

#[test]
fn test_if_command_invalid_missing_body() {
    let mut p = make_parser("if guard; then; elif guard2; then body2; else else; fi");
    assert_eq!(Err(Unexpected(Token::Semi, src(14, 1, 15))), p.if_command());
    let mut p = make_parser("if guard1; then body1; elif; then body2; else else; fi");
    assert_eq!(Err(Unexpected(Token::Semi, src(27, 1, 28))), p.if_command());
    let mut p = make_parser("if guard1; then body1; elif guard2; then body2; else; fi");
    assert_eq!(Err(Unexpected(Token::Semi, src(52, 1, 53))), p.if_command());
}

#[test]
fn test_if_command_invalid_quoted() {
    let cmds = [
        ("'if' guard1; then body1; elif guard2; then body2; else else; fi", Unexpected(Token::SingleQuote, src(0,1,1))),
        ("if guard1; then body1; elif guard2; then body2; else else; 'fi'", IncompleteCmd("if", src(0,1,1), "fi", src(63,1,64))),
        ("\"if\" guard1; then body1; elif guard2; then body2; else else; fi", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("if guard1; then body1; elif guard2; then body2; else else; \"fi\"", IncompleteCmd("if", src(0,1,1), "fi", src(63,1,64))),
    ];

    for &(s, ref e) in cmds.into_iter() {
        match make_parser(s).if_command() {
            Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", s, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       s, e, err);
            },
        }
    }
}

#[test]
fn test_if_command_invalid_concat() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("i")), Token::Literal(String::from("f")),
        Token::Newline, Token::Literal(String::from("guard1")), Token::Newline,
        Token::Literal(String::from("then")),
        Token::Newline, Token::Literal(String::from("body1")), Token::Newline,
        Token::Literal(String::from("elif")),
        Token::Newline, Token::Literal(String::from("guard2")), Token::Newline,
        Token::Literal(String::from("then")),
        Token::Newline, Token::Literal(String::from("body2")), Token::Newline,
        Token::Literal(String::from("else")),
        Token::Newline, Token::Literal(String::from("else part")), Token::Newline,
        Token::Literal(String::from("fi")),
    ));
    assert_eq!(Err(Unexpected(Token::Literal(String::from("i")), src(0,1,1))), p.if_command());

    // Splitting up `then`, `elif`, and `else` tokens makes them
    // get interpreted as arguments, so an explicit error may not be raised
    // although the command will be malformed

    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("if")),
        Token::Newline, Token::Literal(String::from("guard1")), Token::Newline,
        Token::Literal(String::from("then")),
        Token::Newline, Token::Literal(String::from("body1")), Token::Newline,
        Token::Literal(String::from("elif")),
        Token::Newline, Token::Literal(String::from("guard2")), Token::Newline,
        Token::Literal(String::from("then")),
        Token::Newline, Token::Literal(String::from("body2")), Token::Newline,
        Token::Literal(String::from("else")),
        Token::Newline, Token::Literal(String::from("else part")), Token::Newline,
        Token::Literal(String::from("f")), Token::Literal(String::from("i")),
    ));
    assert_eq!(Err(IncompleteCmd("if", src(0,1,1), "fi", src(61,11,3))), p.if_command());
}

#[test]
fn test_if_command_should_recognize_literals_and_names() {
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
                        p.if_command().unwrap();
                    }
                }
            }
        }
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
fn test_for_command_valid_with_words() {
    let mut p = make_parser("for var #var comment\n#prew1\n#prew2\nin one two three #word comment\n#precmd1\n#precmd2\ndo echo $var; done");
    assert_eq!(p.for_command(), Ok(ForFragments {
        var: "var".into(),
        var_comment: Some(Newline(Some("#var comment".into()))),
        words: Some((
            vec!(
                Newline(Some("#prew1".into())),
                Newline(Some("#prew2".into())),
            ),
            vec!(
                word("one"),
                word("two"),
                word("three"),
            ),
            Some(Newline(Some("#word comment".into())))
        )),
        pre_body_comments: vec!(
            Newline(Some("#precmd1".into())),
            Newline(Some("#precmd2".into())),
        ),
        body: vec!(cmd_from_simple(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("echo"), vec!(word_param(Parameter::Var("var".into())))))
        })),
    }));
}

#[test]
fn test_for_command_valid_without_words() {
    let mut p = make_parser("for var #var comment\n#w1\n#w2\ndo echo $var; done");
    assert_eq!(p.for_command(), Ok(ForFragments {
        var: "var".into(),
        var_comment: Some(Newline(Some("#var comment".into()))),
        words: None,
        pre_body_comments: vec!(
            Newline(Some("#w1".into())),
            Newline(Some("#w2".into())),
        ),
        body: vec!(cmd_from_simple(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("echo"), vec!(word_param(Parameter::Var("var".into())))))
        })),
    }));
}

#[test]
fn test_for_command_valid_with_in_but_no_words_with_separator() {
    let mut p = make_parser("for var in\ndo echo $var; done");
    p.for_command().unwrap();
    let mut p = make_parser("for var in;do echo $var; done");
    p.for_command().unwrap();
}

#[test]
fn test_for_command_valid_with_separator() {
    let mut p = make_parser("for var in one two three\ndo echo $var; done");
    p.for_command().unwrap();
    let mut p = make_parser("for var in one two three;do echo $var; done");
    p.for_command().unwrap();
}

#[test]
fn test_for_command_invalid_with_in_no_words_no_with_separator() {
    let mut p = make_parser("for var in do echo $var; done");
    assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "do", src(25,1,26))), p.for_command());
}

#[test]
fn test_for_command_invalid_missing_separator() {
    let mut p = make_parser("for var in one two three do echo $var; done");
    assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "do", src(39,1,40))), p.for_command());
}

#[test]
fn test_for_command_invalid_amp_not_valid_separator() {
    let mut p = make_parser("for var in one two three& do echo $var; done");
    assert_eq!(Err(Unexpected(Token::Amp, src(24, 1, 25))), p.for_command());
}

#[test]
fn test_for_command_invalid_missing_keyword() {
    let mut p = make_parser("var in one two three\ndo echo $var; done");
    assert_eq!(Err(Unexpected(Token::Name(String::from("var")), src(0,1,1))), p.for_command());
}

#[test]
fn test_for_command_invalid_missing_var() {
    let mut p = make_parser("for in one two three\ndo echo $var; done");
    assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "in", src(7,1,8))), p.for_command());
}

#[test]
fn test_for_command_invalid_missing_body() {
    let mut p = make_parser("for var in one two three\n");
    assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "do", src(25,2,1))), p.for_command());
}

#[test]
fn test_for_command_invalid_quoted() {
    let cmds = [
        ("'for' var in one two three\ndo echo $var; done", Unexpected(Token::SingleQuote, src(0,1,1))),
        ("for var 'in' one two three\ndo echo $var; done", IncompleteCmd("for", src(0,1,1), "in", src(8,1,9))),
        ("\"for\" var in one two three\ndo echo $var; done", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("for var \"in\" one two three\ndo echo $var; done", IncompleteCmd("for", src(0,1,1), "in", src(8,1,9))),
    ];

    for &(c, ref e) in cmds.into_iter() {
        match make_parser(c).for_command() {
            Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       c, e, err);
            },
        }
    }
}

#[test]
fn test_for_command_invalid_var_must_be_name() {
    let mut p = make_parser("for 123var in one two three\ndo echo $var; done");
    assert_eq!(Err(BadIdent(String::from("123var"), src(4, 1, 5))), p.for_command());
    let mut p = make_parser("for 'var' in one two three\ndo echo $var; done");
    assert_eq!(Err(Unexpected(Token::SingleQuote, src(4, 1, 5))), p.for_command());
    let mut p = make_parser("for \"var\" in one two three\ndo echo $var; done");
    assert_eq!(Err(Unexpected(Token::DoubleQuote, src(4, 1, 5))), p.for_command());
    let mut p = make_parser("for var*% in one two three\ndo echo $var; done");
    assert_eq!(Err(Unexpected(Token::Star, src(7, 1, 8))), p.for_command());
}

#[test]
fn test_for_command_invalid_concat() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("fo")), Token::Literal(String::from("r")),
        Token::Whitespace(String::from(" ")), Token::Name(String::from("var")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("in")),
        Token::Literal(String::from("one")), Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("two")), Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("three")), Token::Whitespace(String::from(" ")),
        Token::Newline,

        Token::Literal(String::from("do")), Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("echo")), Token::Whitespace(String::from(" ")),
        Token::Dollar, Token::Literal(String::from("var")),
        Token::Newline,
        Token::Literal(String::from("done")),
    ));
    assert_eq!(Err(Unexpected(Token::Literal(String::from("fo")), src(0, 1, 1))), p.for_command());

    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("for")),
        Token::Whitespace(String::from(" ")), Token::Name(String::from("var")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("i")), Token::Literal(String::from("n")),
        Token::Literal(String::from("one")), Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("two")), Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("three")), Token::Whitespace(String::from(" ")),
        Token::Newline,

        Token::Literal(String::from("do")), Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("echo")), Token::Whitespace(String::from(" ")),
        Token::Dollar, Token::Literal(String::from("var")),
        Token::Newline,
        Token::Literal(String::from("done")),
    ));
    assert_eq!(Err(IncompleteCmd("for", src(0,1,1), "in", src(8,1,9))), p.for_command());
}

#[test]
fn test_for_command_should_recognize_literals_and_names() {
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
            p.for_command().unwrap();
        }
    }
}

#[test]
fn test_function_declaration_valid() {
    let correct = FunctionDef(
        String::from("foo"),
        Rc::new(CompoundCommand {
            kind: Brace(vec!(cmd_args("echo", &["body"]))),
            io: vec!(),
        })
    );

    assert_eq!(correct, make_parser("function foo()      { echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo ()     { echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo (    ) { echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo(    )  { echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo        { echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("foo()               { echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("foo ()              { echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("foo (    )          { echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("foo(    )           { echo body; }").function_declaration().unwrap());

    assert_eq!(correct, make_parser("function foo()     \n{ echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo ()    \n{ echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo (    )\n{ echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo(    ) \n{ echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo       \n{ echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("foo()              \n{ echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("foo ()             \n{ echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("foo (    )         \n{ echo body; }").function_declaration().unwrap());
    assert_eq!(correct, make_parser("foo(    )          \n{ echo body; }").function_declaration().unwrap());
}

#[test]
fn test_function_declaration_valid_body_need_not_be_a_compound_command() {
    let src = vec!(
        ("function foo()      echo body;", src(20, 1, 21)),
        ("function foo ()     echo body;", src(20, 1, 21)),
        ("function foo (    ) echo body;", src(20, 1, 21)),
        ("function foo(    )  echo body;", src(20, 1, 21)),
        ("function foo        echo body;", src(20, 1, 21)),
        ("foo()               echo body;", src(20, 1, 21)),
        ("foo ()              echo body;", src(20, 1, 21)),
        ("foo (    )          echo body;", src(20, 1, 21)),
        ("foo(    )           echo body;", src(20, 1, 21)),

        ("function foo()     \necho body;", src(20, 2, 1)),
        ("function foo ()    \necho body;", src(20, 2, 1)),
        ("function foo (    )\necho body;", src(20, 2, 1)),
        ("function foo(    ) \necho body;", src(20, 2, 1)),
        ("function foo       \necho body;", src(20, 2, 1)),
        ("foo()              \necho body;", src(20, 2, 1)),
        ("foo ()             \necho body;", src(20, 2, 1)),
        ("foo (    )         \necho body;", src(20, 2, 1)),
        ("foo(    )          \necho body;", src(20, 2, 1)),
    );

    for (s, p) in src {
        let correct = Unexpected(Token::Name(String::from("echo")), p);
        match make_parser(s).function_declaration() {
            Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
            Err(ref err) => if err != &correct {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       s, correct, err);
            },
        }
    }
}

#[test]
fn test_function_declaration_parens_can_be_subshell_if_function_keyword_present() {
    let correct = FunctionDef(
        String::from("foo"),
        Rc::new(CompoundCommand {
            kind: Subshell(vec!(cmd_args("echo", &["subshell"]))),
            io: vec!(),
        })
    );

    assert_eq!(correct, make_parser("function foo (echo subshell)").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo() (echo subshell)").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo () (echo subshell)").function_declaration().unwrap());
    assert_eq!(correct, make_parser("function foo\n(echo subshell)").function_declaration().unwrap());
}

#[test]
fn test_function_declaration_invalid_newline_in_declaration() {
    let mut p = make_parser("function\nname() { echo body; }");
    assert_eq!(Err(Unexpected(Token::Newline, src(8,1,9))), p.function_declaration());
    // If the function keyword is present the () are optional, and at this particular point
    // they become an empty subshell (which is invalid)
    let mut p = make_parser("function name\n() { echo body; }");
    assert_eq!(Err(Unexpected(Token::ParenClose, src(15,2,2))), p.function_declaration());
}

#[test]
fn test_function_declaration_invalid_missing_space_after_fn_keyword_and_no_parens() {
    let mut p = make_parser("functionname { echo body; }");
    assert_eq!(Err(Unexpected(Token::CurlyOpen, src(13,1,14))), p.function_declaration());
}

#[test]
fn test_function_declaration_invalid_missing_fn_keyword_and_parens() {
    let mut p = make_parser("name { echo body; }");
    assert_eq!(Err(Unexpected(Token::CurlyOpen, src(5,1,6))), p.function_declaration());
}

#[test]
fn test_function_declaration_invalid_missing_space_after_name_no_parens() {
    let mut p = make_parser("function name{ echo body; }");
    assert_eq!(Err(Unexpected(Token::CurlyOpen, src(13,1,14))), p.function_declaration());
    let mut p = make_parser("function name( echo body; )");
    assert_eq!(Err(Unexpected(Token::Name(String::from("echo")), src(15,1,16))), p.function_declaration());
}

#[test]
fn test_function_declaration_invalid_missing_name() {
    let mut p = make_parser("function { echo body; }");
    assert_eq!(Err(Unexpected(Token::CurlyOpen, src(9,1,10))), p.function_declaration());
    let mut p = make_parser("function () { echo body; }");
    assert_eq!(Err(Unexpected(Token::ParenOpen, src(9,1,10))), p.function_declaration());
    let mut p = make_parser("() { echo body; }");
    assert_eq!(Err(Unexpected(Token::ParenOpen, src(0,1,1))), p.function_declaration());
}

#[test]
fn test_function_declaration_invalid_missing_body() {
    let mut p = make_parser("function name");
    assert_eq!(Err(UnexpectedEOF), p.function_declaration());
    let mut p = make_parser("function name()");
    assert_eq!(Err(UnexpectedEOF), p.function_declaration());
    let mut p = make_parser("name()");
    assert_eq!(Err(UnexpectedEOF), p.function_declaration());
}

#[test]
fn test_function_declaration_invalid_quoted() {
    let cmds = [
        ("'function' name { echo body; }", Unexpected(Token::SingleQuote, src(0,1,1))),
        ("function 'name'() { echo body; }", Unexpected(Token::SingleQuote, src(9,1,10))),
        ("name'()' { echo body; }", Unexpected(Token::SingleQuote, src(4,1,5))),
        ("\"function\" name { echo body; }", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("function \"name\"() { echo body; }", Unexpected(Token::DoubleQuote, src(9,1,10))),
        ("name\"()\" { echo body; }", Unexpected(Token::DoubleQuote, src(4,1,5))),
    ];

    for &(c, ref e) in cmds.into_iter() {
        match make_parser(c).function_declaration() {
            Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       c, e, err);
            },
        }
    }
}

#[test]
fn test_function_declaration_invalid_fn_must_be_name() {
    let mut p = make_parser("function 123fn { echo body; }");
    assert_eq!(Err(BadIdent(String::from("123fn"), src(9, 1, 10))), p.function_declaration());
    let mut p = make_parser("function 123fn() { echo body; }");
    assert_eq!(Err(BadIdent(String::from("123fn"), src(9, 1, 10))), p.function_declaration());
    let mut p = make_parser("123fn() { echo body; }");
    assert_eq!(Err(BadIdent(String::from("123fn"), src(0, 1, 1))), p.function_declaration());
}

#[test]
fn test_function_declaration_invalid_fn_name_must_be_name_token() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("function")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("fn_name")),
        Token::Whitespace(String::from(" ")),

        Token::ParenOpen, Token::ParenClose,
        Token::Whitespace(String::from(" ")),
        Token::CurlyOpen,
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("echo")),
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("fn body")),
        Token::Semi,
        Token::CurlyClose,
    ));
    assert_eq!(Err(BadIdent(String::from("fn_name"), src(9, 1, 10))), p.function_declaration());

    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("function")),
        Token::Whitespace(String::from(" ")),

        Token::Name(String::from("fn_name")),
        Token::Whitespace(String::from(" ")),

        Token::ParenOpen, Token::ParenClose,
        Token::Whitespace(String::from(" ")),
        Token::CurlyOpen,
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("echo")),
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("fn body")),
        Token::Semi,
        Token::CurlyClose,
    ));
    p.function_declaration().unwrap();
}

#[test]
fn test_function_declaration_invalid_concat() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("func")), Token::Literal(String::from("tion")),
        Token::Whitespace(String::from(" ")),

        Token::Name(String::from("fn_name")),
        Token::Whitespace(String::from(" ")),

        Token::ParenOpen, Token::ParenClose,
        Token::Whitespace(String::from(" ")),
        Token::CurlyOpen,
        Token::Literal(String::from("echo")),
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("fn body")),
        Token::Semi,
        Token::CurlyClose,
    ));
    assert_eq!(Err(BadIdent(String::from("func"), src(0, 1, 1))), p.function_declaration());
}

#[test]
fn test_function_declaration_should_recognize_literals_and_names_for_fn_keyword() {
    for fn_tok in vec!(Token::Literal(String::from("function")), Token::Name(String::from("function"))) {
        let mut p = make_parser_from_tokens(vec!(
            fn_tok,
            Token::Whitespace(String::from(" ")),

            Token::Name(String::from("fn_name")),
            Token::Whitespace(String::from(" ")),

            Token::ParenOpen, Token::ParenClose,
            Token::Whitespace(String::from(" ")),
            Token::CurlyOpen,
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("fn body")),
            Token::Semi,
            Token::CurlyClose,
        ));
        p.function_declaration().unwrap();
    }
}

#[test]
fn test_case_command_valid() {
    let correct = builder::CaseFragments {
        word: word("foo"),
        post_word_comments: vec!(),
        in_comment: None,
        arms: vec!(
            builder::CaseArm {
                patterns: builder::CasePatternFragments {
                    pre_pattern_comments: vec!(),
                    pattern_alternatives: vec!(word("hello"), word("goodbye")),
                    pattern_comment: None,
                },
                pre_body_comments: vec!(),
                body: vec!(cmd_args("echo", &["greeting"])),
                post_body_comments: vec!(),
                arm_comment: None,
            },
            builder::CaseArm {
                patterns: builder::CasePatternFragments {
                    pre_pattern_comments: vec!(),
                    pattern_alternatives: vec!(word("world")),
                    pattern_comment: None,
                },
                pre_body_comments: vec!(),
                body: vec!(cmd_args("echo", &["noun"])),
                post_body_comments: vec!(),
                arm_comment: None,
            },
        ),
        post_arms_comments: vec!(),
    };

    let cases = vec!(
        // `(` before pattern is optional
        "case foo in  hello | goodbye) echo greeting;;  world) echo noun;; esac",
        "case foo in (hello | goodbye) echo greeting;;  world) echo noun;; esac",
        "case foo in (hello | goodbye) echo greeting;; (world) echo noun;; esac",

        // Final `;;` is optional as long as last command is complete
        "case foo in hello | goodbye) echo greeting;; world) echo noun\nesac",
        "case foo in hello | goodbye) echo greeting;; world) echo noun; esac",
    );

    for src in cases {
        assert_eq!(correct, make_parser(src).case_command().unwrap());
    }
}

#[test]
fn test_case_command_valid_with_comments() {
    let correct = builder::CaseFragments {
        word: word("foo"),
        post_word_comments: vec!(
            Newline(Some(String::from("#word_comment"))),
            Newline(Some(String::from("#post_word_a"))),
            Newline(None),
            Newline(Some(String::from("#post_word_b"))),
        ),
        in_comment: Some(Newline(Some(String::from("#in_comment")))),
        arms: vec!(
            builder::CaseArm {
                patterns: builder::CasePatternFragments {
                    pre_pattern_comments: vec!(
                        Newline(None),
                        Newline(Some(String::from("#pre_pat_a"))),
                    ),
                    pattern_alternatives: vec!(word("hello"), word("goodbye")),
                    pattern_comment: Some(Newline(Some(String::from("#pat_a")))),
                },
                pre_body_comments: vec!(
                    Newline(None),
                    Newline(Some(String::from("#pre_body_a")))
                ),
                body: vec!(cmd_args("echo", &["greeting"])),
                post_body_comments: vec!(),
                arm_comment: Some(Newline(Some(String::from("#arm_a")))),
            },
            builder::CaseArm {
                patterns: builder::CasePatternFragments {
                    pre_pattern_comments: vec!(
                        Newline(None),
                        Newline(Some(String::from("#pre_pat_b"))),
                    ),
                    pattern_alternatives: vec!(word("world")),
                    pattern_comment: Some(Newline(Some(String::from("#pat_b")))),
                },
                pre_body_comments: vec!(
                    Newline(None),
                    Newline(Some(String::from("#pre_body_b")))
                ),
                body: vec!(cmd_args("echo", &["noun"])),
                post_body_comments: vec!(),
                arm_comment: Some(Newline(Some(String::from("#arm_b")))),
            },
        ),
        post_arms_comments: vec!(
            Newline(None),
            Newline(Some(String::from("#post_arms"))),
        ),
    };

    // Various newlines and comments allowed within the command
    let cmd =
        "case foo #word_comment
        #post_word_a

        #post_word_b
        in #in_comment

        #pre_pat_a
        (hello | goodbye) #pat_a

        #pre_body_a
        echo greeting #within_body

        #post_body_a
        ;; #arm_a

        #pre_pat_b
        world) #pat_b

        #pre_body_b
        echo noun;; #arm_b

        #post_arms
        esac";

    assert_eq!(correct, make_parser(cmd).case_command().unwrap());
}

#[test]
fn test_case_command_valid_with_comments_no_body() {
    let correct = builder::CaseFragments {
        word: word("foo"),
        post_word_comments: vec!(
            Newline(Some(String::from("#word_comment"))),
            Newline(Some(String::from("#post_word_a"))),
            Newline(None),
            Newline(Some(String::from("#post_word_b"))),
        ),
        in_comment: Some(Newline(Some(String::from("#in_comment")))),
        arms: vec!(),
        post_arms_comments: vec!(
            Newline(None),
            Newline(Some(String::from("#post_arms"))),
        ),
    };

    // Various newlines and comments allowed within the command
    let cmd =
        "case foo #word_comment
        #post_word_a

        #post_word_b
        in #in_comment

        #post_arms
        esac #case_comment";

    assert_eq!(correct, make_parser(cmd).case_command().unwrap());
}

#[test]
fn test_case_command_word_need_not_be_simple_literal() {
    let mut p = make_parser("case 'foo'bar$$ in foo) echo foo;; esac");
    p.case_command().unwrap();
}

#[test]
fn test_case_command_valid_with_no_arms() {
    let mut p = make_parser("case foo in esac");
    p.case_command().unwrap();
}

#[test]
fn test_case_command_valid_branch_with_no_command() {
    let mut p = make_parser("case foo in pat)\nesac");
    p.case_command().unwrap();
    let mut p = make_parser("case foo in pat);;esac");
    p.case_command().unwrap();
}

#[test]
fn test_case_command_invalid_missing_keyword() {
    let mut p = make_parser("foo in foo) echo foo;; bar) echo bar;; esac");
    assert_eq!(Err(Unexpected(Token::Name(String::from("foo")), src(0, 1, 1))), p.case_command());
    let mut p = make_parser("case foo foo) echo foo;; bar) echo bar;; esac");
    assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "in", src(9,1,10))), p.case_command());
    let mut p = make_parser("case foo in foo) echo foo;; bar) echo bar;;");
    assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "esac", src(43,1,44))), p.case_command());
}

#[test]
fn test_case_command_invalid_missing_word() {
    let mut p = make_parser("case in foo) echo foo;; bar) echo bar;; esac");
    assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "in", src(8,1,9))), p.case_command());
}

#[test]
fn test_case_command_invalid_quoted() {
    let cmds = [
        ("'case' foo in foo) echo foo;; bar) echo bar;; esac", Unexpected(Token::SingleQuote, src(0,1,1))),
        ("case foo 'in' foo) echo foo;; bar) echo bar;; esac", IncompleteCmd("case", src(0,1,1), "in", src(9,1,10))),
        ("case foo in foo) echo foo;; bar')' echo bar;; esac", Unexpected(Token::Name(String::from("echo")), src(35,1,36))),
        ("case foo in foo) echo foo;; bar) echo bar;; 'esac'", IncompleteCmd("case", src(0,1,1), "esac", src(50,1,51))),
        ("\"case\" foo in foo) echo foo;; bar) echo bar;; esac", Unexpected(Token::DoubleQuote, src(0,1,1))),
        ("case foo \"in\" foo) echo foo;; bar) echo bar;; esac", IncompleteCmd("case", src(0,1,1), "in", src(9,1,10))),
        ("case foo in foo) echo foo;; bar\")\" echo bar;; esac", Unexpected(Token::Name(String::from("echo")), src(35,1,36))),
        ("case foo in foo) echo foo;; bar) echo bar;; \"esac\"", IncompleteCmd("case", src(0,1,1), "esac", src(50,1,51))),
    ];

    for &(c, ref e) in cmds.into_iter() {
        match make_parser(c).case_command() {
            Ok(result) => panic!("Unexpectedly parsed \"{}\" as\n{:#?}", c, result),
            Err(ref err) => if err != e {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       c, e, err);
            },
        }
    }
}

#[test]
fn test_case_command_invalid_newline_after_case() {
    let mut p = make_parser("case\nfoo in foo) echo foo;; bar) echo bar;; esac");
    assert_eq!(Err(Unexpected(Token::Newline, src(4, 1, 5))), p.case_command());
}

#[test]
fn test_case_command_invalid_concat() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("ca")), Token::Literal(String::from("se")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("foo")),
        Token::Literal(String::from("bar")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("in")),
        Token::Literal(String::from("foo")),
        Token::ParenClose,
        Token::Newline,
        Token::Literal(String::from("echo")),
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("foo")),
        Token::Newline,
        Token::Newline,
        Token::DSemi,

        Token::Literal(String::from("esac")),
    ));
    assert_eq!(Err(Unexpected(Token::Literal(String::from("ca")), src(0,1,1))), p.case_command());

    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("case")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("foo")),
        Token::Literal(String::from("bar")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("i")), Token::Literal(String::from("n")),
        Token::Literal(String::from("foo")),
        Token::ParenClose,
        Token::Newline,
        Token::Literal(String::from("echo")),
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("foo")),
        Token::Newline,
        Token::Newline,
        Token::DSemi,

        Token::Literal(String::from("esac")),
    ));
    assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "in", src(12,1,13))), p.case_command());

    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("case")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("foo")),
        Token::Literal(String::from("bar")),
        Token::Whitespace(String::from(" ")),

        Token::Literal(String::from("in")),
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

        Token::Literal(String::from("es")), Token::Literal(String::from("ac")),
    ));
    assert_eq!(Err(IncompleteCmd("case", src(0,1,1), "esac", src(36,4,7))), p.case_command());
}

#[test]
fn test_case_command_should_recognize_literals_and_names() {
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
                p.case_command().unwrap();
            }
        }
    }
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
fn test_command_delegates_valid_commands_brace() {
    let correct = Compound(Box::new(CompoundCommand {
        kind: Brace(vec!(cmd("foo"))),
        io: vec!(),
    }));
    assert_eq!(correct, make_parser("{ foo; }").command().unwrap());
}

#[test]
fn test_command_delegates_valid_commands_subshell() {
    let commands = [
        "(foo)",
        "( foo)",
    ];

    let correct = Compound(Box::new(CompoundCommand {
        kind: Subshell(vec!(cmd("foo"))),
        io: vec!(),
    }));

    for cmd in &commands {
        match make_parser(cmd).command() {
            Ok(ref result) if result == &correct => {},
            Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
            Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
        }
    }
}

#[test]
fn test_command_delegates_valid_commands_while() {
    let correct = Compound(Box::new(CompoundCommand {
        kind: While(GuardBodyPair {
            guard: vec!(cmd("guard")),
            body: vec!(cmd("foo")),
        }),
        io: vec!(),
    }));
    assert_eq!(correct, make_parser("while guard; do foo; done").command().unwrap());
}

#[test]
fn test_command_delegates_valid_commands_until() {
    let correct = Compound(Box::new(CompoundCommand {
        kind: Until(GuardBodyPair {
            guard: vec!(cmd("guard")),
            body: vec!(cmd("foo")),
        }),
        io: vec!(),
    }));
    assert_eq!(correct, make_parser("until guard; do foo; done").command().unwrap());
}

#[test]
fn test_command_delegates_valid_commands_for() {
    let correct = Compound(Box::new(CompoundCommand {
        kind: For {
            var: String::from("var"),
            words: Some(vec!()),
            body: vec!(cmd("foo")),
        },
        io: vec!(),
    }));
    assert_eq!(correct, make_parser("for var in; do foo; done").command().unwrap());
}

#[test]
fn test_command_delegates_valid_commands_if() {
    let correct = Compound(Box::new(CompoundCommand {
        kind: If {
            conditionals: vec!(GuardBodyPair {
                guard: vec!(cmd("guard")),
                body: vec!(cmd("body")),
            }),
            else_branch: None,
        },
        io: vec!(),
    }));
    assert_eq!(correct, make_parser("if guard; then body; fi").command().unwrap());
}

#[test]
fn test_command_delegates_valid_commands_case() {
    let correct = Compound(Box::new(CompoundCommand {
        kind: Case {
            word: word("foo"),
            arms: vec!(),
        },
        io: vec!(),
    }));
    assert_eq!(correct, make_parser("case foo in esac").command().unwrap());
}

#[test]
fn test_command_delegates_valid_simple_commands() {
    let correct = Simple(cmd_args_simple("echo", &["foo", "bar"]));
    assert_eq!(correct, make_parser("echo foo bar").command().unwrap());
}

#[test]
fn test_command_delegates_valid_commands_function() {
    let commands = [
        "function foo()      { echo body; }",
        "function foo ()     { echo body; }",
        "function foo (    ) { echo body; }",
        "function foo(    )  { echo body; }",
        "function foo        { echo body; }",
        "foo()               { echo body; }",
        "foo ()              { echo body; }",
        "foo (    )          { echo body; }",
        "foo(    )           { echo body; }",
    ];

    let correct = FunctionDef(String::from("foo"), Rc::new(CompoundCommand {
        kind: Brace(vec!(cmd_args("echo", &["body"]))),
        io: vec!(),
    }));

    for cmd in &commands {
        match make_parser(cmd).command() {
            Ok(ref result) if result == &correct => {},
            Ok(result) => panic!("Parsed \"{}\" as an unexpected command type:\n{:#?}", cmd, result),
            Err(err) => panic!("Failed to parse \"{}\": {}", cmd, err),
        }
    }
}

#[test]
fn test_command_parses_quoted_compound_commands_as_simple_commands() {
    let cases = [
        "{foo; }", // { is a reserved word, thus concatenating it essentially "quotes" it
        "'{' foo; }",
        "'(' foo; )",
        "'while' guard do foo; done",
        "'until' guard do foo; done",
        "'if' guard; then body; fi",
        "'for' var in; do echo $var; done",
        "'function' name { echo body; }",
        "name'()' { echo body; }",
        "123fn() { echo body; }",
        "'case' foo in esac",
        "\"{\" foo; }",
        "\"(\" foo; )",
        "\"while\" guard do foo; done",
        "\"until\" guard do foo; done",
        "\"if\" guard; then body; fi",
        "\"for\" var in; do echo $var; done",
        "\"function\" name { echo body; }",
        "name\"()\" { echo body; }",
        "\"case\" foo in esac",
    ];

    for cmd in &cases {
        match make_parser(cmd).command() {
            Ok(Simple(_)) => {},
            Ok(result) =>
                panic!("Parse::command unexpectedly parsed \"{}\" as a non-simple command:\n{:#?}", cmd, result),
            Err(err) => panic!("Parse::command failed to parse \"{}\": {}", cmd, err),
        }
    }
}

#[test]
fn test_command_should_delegate_literals_and_names_loop_while() {
    for kw in vec!(
        Token::Literal(String::from("while")),
        Token::Name(String::from("while"))
    ) {
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

        let cmd = p.command().unwrap();
        if let Compound(ref compound_cmd) = cmd {
            if let While(..) = compound_cmd.kind {
                continue;
            }
        }

        panic!("Parsed an unexpected command:\n{:#?}", cmd)
    }
}

#[test]
fn test_command_should_delegate_literals_and_names_loop_until() {
    for kw in vec!(
        Token::Literal(String::from("until")),
        Token::Name(String::from("until"))
    ) {
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

        let cmd = p.command().unwrap();
        if let Compound(ref compound_cmd) = cmd {
            if let Until(..) = compound_cmd.kind {
                continue;
            }
        }

        panic!("Parsed an unexpected command:\n{:#?}", cmd)
    }
}

#[test]
fn test_command_should_delegate_literals_and_names_if() {
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

                        let cmd = p.command().unwrap();
                        if let Compound(ref compound_cmd) = cmd {
                            if let If { .. } = compound_cmd.kind {
                                continue;
                            }
                        }

                        panic!("Parsed an unexpected command:\n{:#?}", cmd)
                    }
                }
            }
        }
    }
}

#[test]
fn test_command_should_delegate_literals_and_names_for() {
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

            let cmd = p.command().unwrap();
            if let Compound(ref compound_cmd) = cmd {
                if let For { .. } = compound_cmd.kind {
                    continue;
                }
            }

            panic!("Parsed an unexpected command:\n{:#?}", cmd)
        }
    }
}

#[test]
fn test_command_should_delegate_literals_and_names_case() {
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

                let cmd = p.command().unwrap();
                if let Compound(ref compound_cmd) = cmd {
                    if let Case { .. } = compound_cmd.kind {
                        continue;
                    }
                }

                panic!("Parsed an unexpected command:\n{:#?}", cmd)
            }
        }
    }
}

#[test]
fn test_command_should_delegate_literals_and_names_for_function_declaration() {
    for fn_tok in vec!(Token::Literal(String::from("function")), Token::Name(String::from("function"))) {
        let mut p = make_parser_from_tokens(vec!(
            fn_tok,
            Token::Whitespace(String::from(" ")),

            Token::Name(String::from("fn_name")),
            Token::Whitespace(String::from(" ")),

            Token::ParenOpen, Token::ParenClose,
            Token::Whitespace(String::from(" ")),
            Token::CurlyOpen,
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("echo")),
            Token::Whitespace(String::from(" ")),
            Token::Literal(String::from("fn body")),
            Token::Semi,
            Token::CurlyClose,
        ));
        match p.command() {
            Ok(FunctionDef(..)) => {},
            Ok(result) => panic!("Parsed an unexpected command type:\n{:#?}", result),
            Err(err) => panic!("Failed to parse command: {}", err),
        }
    }
}

#[test]
fn test_command_do_not_delegate_functions_only_if_fn_name_is_a_literal_token() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Literal(String::from("fn_name")),
        Token::Whitespace(String::from(" ")),

        Token::ParenOpen, Token::ParenClose,
        Token::Whitespace(String::from(" ")),
        Token::CurlyOpen,
        Token::Literal(String::from("echo")),
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("fn body")),
        Token::Semi,
        Token::CurlyClose,
    ));
    match p.command() {
        Ok(Simple(..)) => {},
        Ok(result) => panic!("Parsed an unexpected command type:\n{:#?}", result),
        Err(err) => panic!("Failed to parse command: {}", err),
    }
}

#[test]
fn test_command_delegate_functions_only_if_fn_name_is_a_name_token() {
    let mut p = make_parser_from_tokens(vec!(
        Token::Name(String::from("fn_name")),
        Token::Whitespace(String::from(" ")),

        Token::ParenOpen, Token::ParenClose,
        Token::Whitespace(String::from(" ")),
        Token::CurlyOpen,
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("echo")),
        Token::Whitespace(String::from(" ")),
        Token::Literal(String::from("fn body")),
        Token::Semi,
        Token::CurlyClose,
    ));
    match p.command() {
        Ok(FunctionDef(..)) => {},
        Ok(result) => panic!("Parsed an unexpected command type:\n{:#?}", result),
        Err(err) => panic!("Failed to parse command: {}", err),
    }
}

#[test]
fn test_word_single_quote_valid() {
    let correct = single_quoted("abc&&||\n\n#comment\nabc");
    assert_eq!(Some(correct), make_parser("'abc&&||\n\n#comment\nabc'").word().unwrap());
}

#[test]
fn test_word_single_quote_valid_slash_remains_literal() {
    let correct = single_quoted("\\\n");
    assert_eq!(Some(correct), make_parser("'\\\n'").word().unwrap());
}

#[test]
fn test_word_single_quote_valid_does_not_quote_single_quotes() {
    let correct = single_quoted("hello \\");
    assert_eq!(Some(correct), make_parser("'hello \\'").word().unwrap());
}

#[test]
fn test_word_single_quote_invalid_missing_close_quote() {
    assert_eq!(Err(Unmatched(Token::SingleQuote, src(0, 1, 1))), make_parser("'hello").word());
}

#[test]
fn test_word_double_quote_valid() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(Literal(String::from("abc&&||\n\n#comment\nabc"))))));
    assert_eq!(Some(correct), make_parser("\"abc&&||\n\n#comment\nabc\"").word().unwrap());
}

#[test]
fn test_word_double_quote_valid_recognizes_parameters() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
        Literal(String::from("test asdf")),
        Param(Parameter::Var(String::from("foo"))),
        Literal(String::from(" $")),
    ))));

    assert_eq!(Some(correct), make_parser("\"test asdf$foo $\"").word().unwrap());
}

#[test]
fn test_word_double_quote_valid_recognizes_backticks() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
        Literal(String::from("test asdf ")),
        Subst(Box::new(ParameterSubstitution::Command(vec!(cmd("foo"))))),
    ))));

    assert_eq!(Some(correct), make_parser("\"test asdf `foo`\"").word().unwrap());
}

#[test]
fn test_word_double_quote_valid_slash_escapes_dollar() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
        Literal(String::from("test")),
        Escaped(String::from("$")),
        Literal(String::from("foo ")),
        Param(Parameter::At),
    ))));

    assert_eq!(Some(correct), make_parser("\"test\\$foo $@\"").word().unwrap());
}

#[test]
fn test_word_double_quote_valid_slash_escapes_backtick() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
        Literal(String::from("test")),
        Escaped(String::from("`")),
        Literal(String::from(" ")),
        Param(Parameter::Star),
    ))));

    assert_eq!(Some(correct), make_parser("\"test\\` $*\"").word().unwrap());
}

#[test]
fn test_word_double_quote_valid_slash_escapes_double_quote() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
        Literal(String::from("test")),
        Escaped(String::from("\"")),
        Literal(String::from(" ")),
        Param(Parameter::Pound),
    ))));

    assert_eq!(Some(correct), make_parser("\"test\\\" $#\"").word().unwrap());
}

#[test]
fn test_word_double_quote_valid_slash_escapes_newline() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
        Literal(String::from("test")),
        Escaped(String::from("\n")),
        Literal(String::from(" ")),
        Param(Parameter::Question),
        Literal(String::from("\n")),
    ))));

    assert_eq!(Some(correct), make_parser("\"test\\\n $?\n\"").word().unwrap());
}

#[test]
fn test_word_double_quote_valid_slash_escapes_slash() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
        Literal(String::from("test")),
        Escaped(String::from("\\")),
        Literal(String::from(" ")),
        Param(Parameter::Positional(0)),
    ))));

    assert_eq!(Some(correct), make_parser("\"test\\\\ $0\"").word().unwrap());
}

#[test]
fn test_word_double_quote_valid_slash_remains_literal_in_general_case() {
    let correct = TopLevelWord(Single(Word::DoubleQuoted(vec!(
        Literal(String::from("t\\est ")),
        Param(Parameter::Dollar),
    ))));

    assert_eq!(Some(correct), make_parser("\"t\\est $$\"").word().unwrap());
}

#[test]
fn test_word_double_quote_slash_invalid_missing_close_quote() {
    assert_eq!(Err(Unmatched(Token::DoubleQuote, src(0, 1, 1))), make_parser("\"hello").word());
    assert_eq!(Err(Unmatched(Token::DoubleQuote, src(0, 1, 1))), make_parser("\"hello\\\"").word());
}

#[test]
fn test_word_delegate_parameters() {
    let params = [
        "$@",
        "$*",
        "$#",
        "$?",
        "$-",
        "$$",
        "$!",
        "$3",
        "${@}",
        "${*}",
        "${#}",
        "${?}",
        "${-}",
        "${$}",
        "${!}",
        "${foo}",
        "${3}",
        "${1000}",
    ];

    for p in params.into_iter() {
        match make_parser(p).word() {
            Ok(Some(TopLevelWord(Single(Word::Simple(w))))) => if let Param(_) = w {} else {
                panic!("Unexpectedly parsed \"{}\" as a non-parameter word:\n{:#?}", p, w);
            },
            Ok(Some(w)) => panic!("Unexpectedly parsed \"{}\" as a non-parameter word:\n{:#?}", p, w),
            Ok(None) => panic!("Did not parse \"{}\" as a parameter", p),
            Err(e) => panic!("Did not parse \"{}\" as a parameter: {}", p, e),
        }
    }
}

#[test]
fn test_word_literal_dollar_if_not_param() {
    let correct = word("$%asdf");
    assert_eq!(correct, make_parser("$%asdf").word().unwrap().unwrap());
}

#[test]
fn test_word_does_not_capture_comments() {
    assert_eq!(Ok(None), make_parser("#comment\n").word());
    assert_eq!(Ok(None), make_parser("  #comment\n").word());
    let mut p = make_parser("word   #comment\n");
    p.word().unwrap().unwrap();
    assert_eq!(Ok(None), p.word());
}

#[test]
fn test_word_pound_in_middle_is_not_comment() {
    let correct = word("abc#def");
    assert_eq!(Ok(Some(correct)), make_parser("abc#def\n").word());
}

#[test]
fn test_word_tokens_which_become_literal_words() {
    let words = [
        "{",
        "}",
        "!",
        "name",
        "1notname",
    ];

    for w in words.into_iter() {
        match make_parser(w).word() {
            Ok(Some(res)) => {
                let correct = word(*w);
                if correct != res {
                    panic!("Unexpectedly parsed \"{}\": expected:\n{:#?}\ngot:\n{:#?}", w, correct, res);
                }
            },
            Ok(None) => panic!("Did not parse \"{}\" as a word", w),
            Err(e) => panic!("Did not parse \"{}\" as a word: {}", w, e),
        }
    }
}

#[test]
fn test_word_concatenation_works() {
    let correct = TopLevelWord(Concat(vec!(
        lit("foo=bar"),
        Word::DoubleQuoted(vec!(Literal(String::from("double")))),
        Word::SingleQuoted(String::from("single")),
    )));

    assert_eq!(Ok(Some(correct)), make_parser("foo=bar\"double\"'single'").word());
}

#[test]
fn test_word_special_words_recognized_as_such() {
    assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Star))))),        make_parser("*").word());
    assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Question))))),    make_parser("?").word());
    assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Tilde))))),       make_parser("~").word());
    assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(SquareOpen))))),  make_parser("[").word());
    assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(SquareClose))))), make_parser("]").word());
    assert_eq!(Ok(Some(TopLevelWord(Single(Word::Simple(Colon))))),       make_parser(":").word());
}

#[test]
fn test_word_backslash_makes_things_literal() {
    let lit = [
        "a",
        "&",
        ";",
        "(",
        "*",
        "?",
        "$",
    ];

    for l in lit.into_iter() {
        let src = format!("\\{}", l);
        match make_parser(&src).word() {
            Ok(Some(res)) => {
                let correct = word_escaped(l);
                if correct != res {
                    panic!("Unexpectedly parsed \"{}\": expected:\n{:#?}\ngot:\n{:#?}", src, correct, res);
                }
            },
            Ok(None) => panic!("Did not parse \"{}\" as a word", src),
            Err(e) => panic!("Did not parse \"{}\" as a word: {}", src, e),
        }
    }
}

#[test]
fn test_word_escaped_newline_becomes_whitespace() {
    let mut p = make_parser("foo\\\nbar");
    assert_eq!(Ok(Some(word("foo"))), p.word());
    assert_eq!(Ok(Some(word("bar"))), p.word());
}

#[test]
fn test_backticked_valid() {
    let correct = word_subst(ParameterSubstitution::Command(vec!(cmd("foo"))));
    assert_eq!(correct, make_parser("`foo`").backticked_command_substitution().unwrap());
}

#[test]
fn test_backticked_valid_backslashes_removed_if_before_dollar_backslash_and_backtick() {
    let correct = word_subst(ParameterSubstitution::Command(vec!(cmd_from_simple(SimpleCommand {
        vars: vec!(), io: vec!(),
        cmd: Some((word("foo"), vec!(
            TopLevelWord(Concat(vec!(
                Word::Simple(Param(Parameter::Dollar)),
                escaped("`"),
                escaped("o"),
            )))
        ))),
    }))));
    assert_eq!(correct, make_parser("`foo \\$\\$\\\\\\`\\o`").backticked_command_substitution().unwrap());
}

#[test]
fn test_backticked_nested_backticks() {
    let correct = word_subst(ParameterSubstitution::Command(vec!(
        cmd_from_simple(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("foo"), vec!(
                word_subst(
                    ParameterSubstitution::Command(vec!(cmd_from_simple(SimpleCommand {
                        vars: vec!(), io: vec!(),
                        cmd: Some((word("bar"), vec!(TopLevelWord(Concat(vec!(escaped("$"), escaped("$")))))))
                    })))
                )
            ))),
        })
    )));
    assert_eq!(correct, make_parser(r#"`foo \`bar \\\\$\\\\$\``"#).backticked_command_substitution().unwrap());
}

#[test]
fn test_backticked_nested_backticks_x2() {
    let correct = word_subst(ParameterSubstitution::Command(vec!(
        cmd_from_simple(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("foo"), vec!(word_subst(
                ParameterSubstitution::Command(vec!(cmd_from_simple(SimpleCommand {
                    vars: vec!(), io: vec!(),
                    cmd: Some((word("bar"), vec!(word_subst(
                        ParameterSubstitution::Command(vec!(cmd_from_simple(SimpleCommand {
                            vars: vec!(), io: vec!(),
                            cmd: Some((word("baz"), vec!(TopLevelWord(Concat(vec!(escaped("$"), escaped("$")))))))
                        })))
                    ))))
                })))
            ))))
        })
    )));
    assert_eq!(correct, make_parser(r#"`foo \`bar \\\`baz \\\\\\\\$\\\\\\\\$ \\\`\``"#).backticked_command_substitution().unwrap());
}

#[test]
fn test_backticked_nested_backticks_x3() {
    let correct = word_subst(ParameterSubstitution::Command(vec!(
        cmd_from_simple(SimpleCommand {
            vars: vec!(), io: vec!(),
            cmd: Some((word("foo"), vec!(word_subst(
                ParameterSubstitution::Command(vec!(cmd_from_simple(SimpleCommand {
                    vars: vec!(), io: vec!(),
                    cmd: Some((word("bar"), vec!(word_subst(
                        ParameterSubstitution::Command(vec!(cmd_from_simple(SimpleCommand {
                            vars: vec!(), io: vec!(),
                            cmd: Some((word("baz"), vec!(word_subst(
                                ParameterSubstitution::Command(vec!(cmd_from_simple(SimpleCommand {
                                    vars: vec!(), io: vec!(),
                                    cmd: Some((word("qux"), vec!(TopLevelWord(Concat(vec!(escaped("$"), escaped("$")))))))
                                })))
                            )))),
                        })))
                    ))))
                })))
            ))))
        })
    )));
    assert_eq!(correct, make_parser(
        r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$\\\\\\\\\\\\\\\\$ \\\\\\\` \\\`\``"#
    ).backticked_command_substitution().unwrap());
}

#[test]
fn test_backticked_invalid_missing_closing_backtick() {
    let src = [
        // Missing outermost backtick
        (r#"`foo"#, src(0,1,1)),
        (r#"`foo \`bar \\\\$\\\\$\`"#, src(0,1,1)),
        (r#"`foo \`bar \\\`baz \\\\\\\\$\\\\\\\\$ \\\`\`"#, src(0,1,1)),
        (r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$ \\\\\\\\\\\\\\\\$ \\\\\\\` \\\`\`"#, src(0,1,1)),

        // Missing second to last backtick
        (r#"`foo \`bar \\\\$\\\\$`"#, src(6,1,7)),
        (r#"`foo \`bar \\\`baz \\\\\\\\$\\\\\\\\$ \\\``"#, src(6,1,7)),
        (r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$ \\\\\\\\\\\\\\\\$ \\\\\\\` \\\``"#, src(6,1,7)),

        // Missing third to last backtick
        (r#"`foo \`bar \\\`baz \\\\\\\\$\\\\\\\\$ \``"#, src(14,1,15)),
        (r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$ \\\\\\\\\\\\\\\\$ \\\\\\\` \``"#, src(14,1,15)),

        // Missing fourth to last backtick
        (r#"`foo \`bar \\\`baz \\\\\\\`qux \\\\\\\\\\\\\\\\$ \\\\\\\\\\\\\\\\$ \\\`\``"#, src(26,1,27)),
    ];

    for &(s, p) in &src {
        let correct = Unmatched(Token::Backtick, p);
        match make_parser(s).backticked_command_substitution() {
            Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
            Err(ref err) => if err != &correct {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       s, correct, err);
            },
        }
    }
}

#[test]
fn test_backticked_invalid_maintains_accurate_source_positions() {
    let src = [
        (r#"`foo ${invalid param}`"#, src(14,1,15)),
        (r#"`foo \`bar ${invalid param}\``"#, src(20,1,21)),
        (r#"`foo \`bar \\\`baz ${invalid param} \\\`\``"#, src(28,1,29)),
        (r#"`foo \`bar \\\`baz \\\\\\\`qux ${invalid param} \\\\\\\` \\\`\``"#, src(40,1,41)),
    ];

    for &(s, p) in &src {
        let correct = BadSubst(Token::Whitespace(String::from(" ")), p);
        match make_parser(s).backticked_command_substitution() {
            Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
            Err(ref err) => if err != &correct {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       s, correct, err);
            },
        }
    }
}

#[test]
fn test_backticked_invalid_missing_opening_backtick() {
    let mut p = make_parser("foo`");
    assert_eq!(
        Err(Unexpected(Token::Name(String::from("foo")), src(0,1,1))),
        p.backticked_command_substitution()
    );
}

#[test]
fn test_arithmetic_substitution_valid() {
    use shell_lang::ast::Arithmetic::*;

    fn x() -> Box<Arithmetic> { Box::new(Var(String::from("x"))) }
    fn y() -> Box<Arithmetic> { Box::new(Var(String::from("y"))) }
    fn z() -> Box<Arithmetic> { Box::new(Var(String::from("z"))) }

    let cases = vec!(
        ("$(( x ))", *x()),
        ("$(( 5 ))",   Literal(5)),
        ("$(( 0 ))",   Literal(0)),
        ("$(( 010 ))", Literal(8)),
        ("$(( 0xa ))", Literal(10)),
        ("$(( 0Xa ))", Literal(10)),
        ("$(( 0xA ))", Literal(10)),
        ("$(( 0XA ))", Literal(10)),
        ("$(( x++ ))", PostIncr(String::from("x"))),
        ("$(( x-- ))", PostDecr(String::from("x"))),
        ("$(( ++x ))", PreIncr(String::from("x"))),
        ("$(( --x ))", PreDecr(String::from("x"))),
        ("$(( +x ))", UnaryPlus(x())),
        ("$(( -x ))", UnaryMinus(x())),
        ("$(( !x ))", LogicalNot(x())),
        ("$(( ~x ))", BitwiseNot(x())),
        ("$(( x ** y))", Pow(x(), y())),
        ("$(( x * y ))", Mult(x(), y())),
        ("$(( x / y ))", Div(x(), y())),
        ("$(( x % y ))", Modulo(x(), y())),
        ("$(( x + y ))", Add(x(), y())),
        ("$(( x - y ))", Sub(x(), y())),
        ("$(( x << y ))", ShiftLeft(x(), y())),
        ("$(( x >> y ))", ShiftRight(x(), y())),
        ("$(( x < y ))", Less(x(), y())),
        ("$(( x <= y ))", LessEq(x(), y())),
        ("$(( x > y ))", Great(x(), y())),
        ("$(( x >= y ))", GreatEq(x(), y())),
        ("$(( x == y ))", Eq(x(), y())),
        ("$(( x != y ))", NotEq(x(), y())),
        ("$(( x & y ))", BitwiseAnd(x(), y())),
        ("$(( x ^ y ))", BitwiseXor(x(), y())),
        ("$(( x | y ))", BitwiseOr(x(), y())),
        ("$(( x && y ))", LogicalAnd(x(), y())),
        ("$(( x || y ))", LogicalOr(x(), y())),
        ("$(( x ? y : z ))", Ternary(x(), y(), z())),
        ("$(( x = y ))",   Assign(String::from("x"), y())),
        ("$(( x *= y ))",  Assign(String::from("x"), Box::new(Mult(x(), y())))),
        ("$(( x /= y ))",  Assign(String::from("x"), Box::new(Div(x(), y())))),
        ("$(( x %= y ))",  Assign(String::from("x"), Box::new(Modulo(x(), y())))),
        ("$(( x += y ))",  Assign(String::from("x"), Box::new(Add(x(), y())))),
        ("$(( x -= y ))",  Assign(String::from("x"), Box::new(Sub(x(), y())))),
        ("$(( x <<= y ))", Assign(String::from("x"), Box::new(ShiftLeft(x(), y())))),
        ("$(( x >>= y ))", Assign(String::from("x"), Box::new(ShiftRight(x(), y())))),
        ("$(( x &= y ))",  Assign(String::from("x"), Box::new(BitwiseAnd(x(), y())))),
        ("$(( x ^= y ))",  Assign(String::from("x"), Box::new(BitwiseXor(x(), y())))),
        ("$(( x |= y ))",  Assign(String::from("x"), Box::new(BitwiseOr(x(), y())))),
        ("$(( x = 5, x + y ))", Sequence(vec!(
                Assign(String::from("x"), Box::new(Literal(5))),
                Add(x(), y())
        ))),
        ("$(( x + (y - z) ))", Add(x(), Box::new(Sub(y(), z())))),
    );

    for (s, a) in cases.into_iter() {
        let correct = word_subst(ParameterSubstitution::Arith(Some(a)));
        match make_parser(s).parameter() {
            Ok(w) => if w != correct {
                panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", s, w, correct)
            },
            Err(err) => panic!("Failed to parse the source \"{}\": {}", s, err),
        }
    }

    let correct = word_subst(ParameterSubstitution::Arith(None));
    assert_eq!(correct, make_parser("$(( ))").parameter().unwrap());
}

#[test]
fn test_arithmetic_substitution_left_to_right_associativity() {
    use shell_lang::ast::Arithmetic::*;

    fn x() -> Box<Arithmetic> { Box::new(Var(String::from("x"))) }
    fn y() -> Box<Arithmetic> { Box::new(Var(String::from("y"))) }
    fn z() -> Box<Arithmetic> { Box::new(Var(String::from("z"))) }

    macro_rules! check {
        ($constructor:path, $op:tt) => {{
            let correct = word_subst(ParameterSubstitution::Arith(Some(
                $constructor(Box::new($constructor(x(), y())), z())
            )));

            let src = format!("$((x {0} y {0} z))", stringify!($op));
            match make_parser(&src).parameter() {
                Ok(w) => if w != correct {
                    panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", src, w, correct)
                },
                Err(err) => panic!("Failed to parse the source \"{}\": {}", src, err),
            }
        }};

        (assig: $constructor:path, $op:tt) => {{
            let correct = word_subst(ParameterSubstitution::Arith(Some(
                Assign(String::from("x"), Box::new(
                    $constructor(x(), Box::new(Assign(String::from("y"), Box::new($constructor(y(), z())))))
                ))
            )));

            let src = format!("$((x {0}= y {0}= z))", stringify!($op));
            match make_parser(&src).parameter() {
                Ok(w) => if w != correct {
                    panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", src, w, correct)
                },
                Err(err) => panic!("Failed to parse the source \"{}\": {}", src, err),
            }
        }};
    }

    check!(Mult,       * );
    check!(Div,        / );
    check!(Modulo,     % );
    check!(Add,        + );
    check!(Sub,        - );
    check!(ShiftLeft,  <<);
    check!(ShiftRight, >>);
    check!(Less,       < );
    check!(LessEq,     <=);
    check!(Great ,     > );
    check!(GreatEq,    >=);
    check!(Eq,         ==);
    check!(NotEq,      !=);
    check!(BitwiseAnd, & );
    check!(BitwiseXor, ^ );
    check!(BitwiseOr,  | );
    check!(LogicalAnd, &&);
    check!(LogicalOr,  ||);

    check!(assig: Mult,       * );
    check!(assig: Div,        / );
    check!(assig: Modulo,     % );
    check!(assig: Add,        + );
    check!(assig: Sub,        - );
    check!(assig: ShiftLeft,  <<);
    check!(assig: ShiftRight, >>);
    check!(assig: BitwiseAnd, & );
    check!(assig: BitwiseXor, ^ );
    check!(assig: BitwiseOr,  | );

    let correct = word_subst(ParameterSubstitution::Arith(Some(
        Assign(String::from("x"), Box::new(Assign(String::from("y"), z())))
    )));
    assert_eq!(correct, make_parser("$(( x = y = z ))").parameter().unwrap());
}

#[test]
fn test_arithmetic_substitution_right_to_left_associativity() {
    use shell_lang::ast::Arithmetic::*;

    fn x() -> Box<Arithmetic> { Box::new(Var(String::from("x"))) }
    fn y() -> Box<Arithmetic> { Box::new(Var(String::from("y"))) }
    fn z() -> Box<Arithmetic> { Box::new(Var(String::from("z"))) }
    fn w() -> Box<Arithmetic> { Box::new(Var(String::from("w"))) }
    fn v() -> Box<Arithmetic> { Box::new(Var(String::from("v"))) }

    let cases = vec!(
        ("$(( x ** y ** z ))", Pow(x(), Box::new(Pow(y(), z())))),
        ("$(( x ? y ? z : w : v ))", Ternary(x(), Box::new(Ternary(y(), z(), w())), v())),
    );

    for (s, a) in cases.into_iter() {
        let correct = word_subst(ParameterSubstitution::Arith(Some(a)));
        match make_parser(s).parameter() {
            Ok(w) => if w != correct {
                panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", s, w, correct)
            },
            Err(err) => panic!("Failed to parse the source \"{}\": {}", s, err),
        }
    }
}

#[test]
fn test_arithmetic_substitution_invalid() {
    let cases = vec!(
        // Pre/post increment/decrement must be applied on a variable
        // Otherwise becomes `expr+(+expr)` or `expr-(-expr)`
        ("$(( 5++ ))", Unexpected(Token::ParenClose, src(8,1,9))),
        ("$(( 5-- ))", Unexpected(Token::ParenClose, src(8,1,9))),
        ("$(( (x + y)++ ))", Unexpected(Token::ParenClose, src(14,1,15))),
        ("$(( (x + y)-- ))", Unexpected(Token::ParenClose, src(14,1,15))),

        // Pre/post increment/decrement must be applied on a variable
        ("$(( ++5 ))", Unexpected(Token::Literal(String::from("5")), src(6,1,7))),
        ("$(( --5 ))", Unexpected(Token::Literal(String::from("5")), src(6,1,7))),
        ("$(( ++(x + y) ))", Unexpected(Token::ParenOpen, src(6,1,7))),
        ("$(( --(x + y) ))", Unexpected(Token::ParenOpen, src(6,1,7))),

        // Incomplete commands
        ("$(( + ))", Unexpected(Token::ParenClose, src(6,1,7))),
        ("$(( - ))", Unexpected(Token::ParenClose, src(6,1,7))),
        ("$(( ! ))", Unexpected(Token::ParenClose, src(6,1,7))),
        ("$(( ~ ))", Unexpected(Token::ParenClose, src(6,1,7))),
        ("$(( x ** ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x *  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x /  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x %  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x +  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x -  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x << ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x >> ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x <  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x <= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x >  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x >= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x == ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x != ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x &  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x ^  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x |  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x && ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x || ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x =  ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x *= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x /= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x %= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x += ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x -= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x <<=))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x >>=))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x &= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x ^= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x |= ))", Unexpected(Token::ParenClose, src(9,1,10))),
        ("$(( x ? y : ))", Unexpected(Token::ParenClose, src(12,1,13))),
        ("$(( x ?     ))", Unexpected(Token::ParenClose, src(12,1,13))),
        ("$(( x = 5, ))", Unexpected(Token::ParenClose, src(11,1,12))),
        ("$(( x + () ))", Unexpected(Token::ParenClose, src(9,1,10))),

        // Missing first operand
        ("$(( ** y  ))", Unexpected(Token::Star, src(4,1,5))),
        ("$(( * y   ))", Unexpected(Token::Star, src(4,1,5))),
        ("$(( / y   ))", Unexpected(Token::Slash, src(4,1,5))),
        ("$(( % y   ))", Unexpected(Token::Percent, src(4,1,5))),
        ("$(( << y  ))", Unexpected(Token::DLess, src(4,1,5))),
        ("$(( >> y  ))", Unexpected(Token::DGreat, src(4,1,5))),
        ("$(( < y   ))", Unexpected(Token::Less, src(4,1,5))),
        ("$(( <= y  ))", Unexpected(Token::Less, src(4,1,5))),
        ("$(( > y   ))", Unexpected(Token::Great, src(4,1,5))),
        ("$(( >= y  ))", Unexpected(Token::Great, src(4,1,5))),
        ("$(( == y  ))", Unexpected(Token::Equals, src(4,1,5))),
        ("$(( & y   ))", Unexpected(Token::Amp, src(4,1,5))),
        ("$(( ^ y   ))", Unexpected(Token::Caret, src(4,1,5))),
        ("$(( | y   ))", Unexpected(Token::Pipe, src(4,1,5))),
        ("$(( && y  ))", Unexpected(Token::AndIf, src(4,1,5))),
        ("$(( || y  ))", Unexpected(Token::OrIf, src(4,1,5))),
        ("$(( = y   ))", Unexpected(Token::Equals, src(4,1,5))),
        ("$(( *= y  ))", Unexpected(Token::Star, src(4,1,5))),
        ("$(( /= y  ))", Unexpected(Token::Slash, src(4,1,5))),
        ("$(( %= y  ))", Unexpected(Token::Percent, src(4,1,5))),
        ("$(( <<= y ))", Unexpected(Token::DLess, src(4,1,5))),
        ("$(( >>= y ))", Unexpected(Token::DGreat, src(4,1,5))),
        ("$(( &= y  ))", Unexpected(Token::Amp, src(4,1,5))),
        ("$(( ^= y  ))", Unexpected(Token::Caret, src(4,1,5))),
        ("$(( |= y  ))", Unexpected(Token::Pipe, src(4,1,5))),
        ("$(( ? y : z ))", Unexpected(Token::Question, src(4,1,5))),
        ("$(( , x + y ))", Unexpected(Token::Comma, src(4,1,5))),

        // Each of the following leading tokens will be parsed as unary
        // operators, thus the error will occur on the `=`.
        ("$(( != y  ))", Unexpected(Token::Equals, src(5,1,6))),
        ("$(( += y  ))", Unexpected(Token::Equals, src(5,1,6))),
        ("$(( -= y  ))", Unexpected(Token::Equals, src(5,1,6))),
    );

    for (s, correct) in cases.into_iter() {
        match make_parser(s).parameter() {
            Ok(w) => panic!("Unexpectedly parsed the source \"{}\" as\n{:?}", s, w),
            Err(ref err) => if err != &correct {
                panic!("Expected the source \"{}\" to return the error `{:?}`, but got `{:?}`",
                       s, correct, err);
            },
        }
    }
}

#[test]
fn test_arithmetic_substitution_precedence() {
    use shell_lang::ast::Arithmetic::*;

    fn var(x: &str) -> Box<Arithmetic> { Box::new(Var(String::from(x))) }

    let cases = vec!(
        ("~o++",   BitwiseNot(Box::new(PostIncr(String::from("o"))))),
        ("~(o+p)", BitwiseNot(Box::new(Add(var("o"), var("p"))))),
        ("-o++",   UnaryMinus(Box::new(PostIncr(String::from("o"))))),
        ("-(o+p)", UnaryMinus(Box::new(Add(var("o"), var("p"))))),
        ("++o",    PreIncr(String::from("o"))),
    );

    for (s, end) in cases.into_iter() {
        let correct = word_subst(ParameterSubstitution::Arith(Some(
            Sequence(vec!(
                *var("x"),
                Assign(String::from("a"), Box::new(
                    Ternary(var("b"), var("c"), Box::new(
                        LogicalOr(var("d"), Box::new(
                            LogicalAnd(var("e"), Box::new(
                                BitwiseOr(var("f"), Box::new(
                                    BitwiseXor(var("g"), Box::new(
                                        BitwiseAnd(var("h"), Box::new(
                                            Eq(var("i"), Box::new(
                                                Less(var("j"), Box::new(
                                                    ShiftLeft(var("k"), Box::new(
                                                        Add(var("l"), Box::new(
                                                            Mult(var("m"), Box::new(
                                                                Pow(var("n"), Box::new(end))
                                                            ))
                                                        ))
                                                    ))
                                                ))
                                            ))
                                        ))
                                    ))
                                ))
                            ))
                        ))
                    ))
                ))
            ))
        )));

        let src = format!("$(( x , a = b?c: d || e && f | g ^ h & i == j < k << l + m * n ** {} ))", s);
        match make_parser(&src).parameter() {
            Ok(w) => if w != correct {
                panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", src, w, correct)
            },
            Err(err) => panic!("Failed to parse the source \"{}\": {}", src, err),
        }
    }
}

#[test]
fn test_arithmetic_substitution_operators_of_equal_precedence() {
    use shell_lang::ast::Arithmetic::*;

    fn x() -> Box<Arithmetic> { Box::new(Var(String::from("x"))) }
    fn y() -> Box<Arithmetic> { Box::new(Var(String::from("y"))) }
    fn z() -> Box<Arithmetic> { Box::new(Var(String::from("z"))) }
    fn w() -> Box<Arithmetic> { Box::new(Var(String::from("w"))) }

    let cases = vec!(
        ("$(( x != y == z ))", Eq(Box::new(NotEq(x(), y())), z())),
        ("$(( x == y != z ))", NotEq(Box::new(Eq(x(), y())), z())),

        ("$(( x <  y < z ))", Less(Box::new(Less(x(), y())), z())),
        ("$(( x <= y < z ))", Less(Box::new(LessEq(x(), y())), z())),
        ("$(( x >  y < z ))", Less(Box::new(Great(x(), y())), z())),
        ("$(( x >= y < z ))", Less(Box::new(GreatEq(x(), y())), z())),

        ("$(( x << y >> z ))", ShiftRight(Box::new(ShiftLeft(x(), y())), z())),
        ("$(( x >> y << z ))", ShiftLeft(Box::new(ShiftRight(x(), y())), z())),

        ("$(( x + y - z ))", Sub(Box::new(Add(x(), y())), z())),
        ("$(( x - y + z ))", Add(Box::new(Sub(x(), y())), z())),

        ("$(( x * y / z % w ))", Modulo(Box::new(Div(Box::new(Mult(x(), y())), z())), w())),
        ("$(( x * y % z / w ))", Div(Box::new(Modulo(Box::new(Mult(x(), y())), z())), w())),
        ("$(( x / y * z % w ))", Modulo(Box::new(Mult(Box::new(Div(x(), y())), z())), w())),
        ("$(( x / y % z * w ))", Mult(Box::new(Modulo(Box::new(Div(x(), y())), z())), w())),
        ("$(( x % y * z / w ))", Div(Box::new(Mult(Box::new(Modulo(x(), y())), z())), w())),
        ("$(( x % y / z * w ))", Mult(Box::new(Div(Box::new(Modulo(x(), y())), z())), w())),

        ("$(( +!~x ))", UnaryPlus(Box::new(LogicalNot(Box::new(BitwiseNot(x())))))),
        ("$(( +~!x ))", UnaryPlus(Box::new(BitwiseNot(Box::new(LogicalNot(x())))))),
        ("$(( !+~x ))", LogicalNot(Box::new(UnaryPlus(Box::new(BitwiseNot(x())))))),
        ("$(( !~+x ))", LogicalNot(Box::new(BitwiseNot(Box::new(UnaryPlus(x())))))),
        ("$(( ~+!x ))", BitwiseNot(Box::new(UnaryPlus(Box::new(LogicalNot(x())))))),
        ("$(( ~!+x ))", BitwiseNot(Box::new(LogicalNot(Box::new(UnaryPlus(x())))))),

        ("$(( -!~x ))", UnaryMinus(Box::new(LogicalNot(Box::new(BitwiseNot(x())))))),
        ("$(( -~!x ))", UnaryMinus(Box::new(BitwiseNot(Box::new(LogicalNot(x())))))),
        ("$(( !-~x ))", LogicalNot(Box::new(UnaryMinus(Box::new(BitwiseNot(x())))))),
        ("$(( !~-x ))", LogicalNot(Box::new(BitwiseNot(Box::new(UnaryMinus(x())))))),
        ("$(( ~-!x ))", BitwiseNot(Box::new(UnaryMinus(Box::new(LogicalNot(x())))))),
        ("$(( ~!-x ))", BitwiseNot(Box::new(LogicalNot(Box::new(UnaryMinus(x())))))),

        ("$(( !~++x ))", LogicalNot(Box::new(BitwiseNot(Box::new(PreIncr(String::from("x"))))))),
        ("$(( ~!++x ))", BitwiseNot(Box::new(LogicalNot(Box::new(PreIncr(String::from("x"))))))),
        ("$(( !~--x ))", LogicalNot(Box::new(BitwiseNot(Box::new(PreDecr(String::from("x"))))))),
        ("$(( ~!--x ))", BitwiseNot(Box::new(LogicalNot(Box::new(PreDecr(String::from("x"))))))),

        ("$(( -+x ))", UnaryMinus(Box::new(UnaryPlus(x())))),
        ("$(( +-x ))", UnaryPlus(Box::new(UnaryMinus(x())))),
    );

    for (s, a) in cases.into_iter() {
        let correct = word_subst(ParameterSubstitution::Arith(Some(a)));
        match make_parser(s).parameter() {
            Ok(w) => if w != correct {
                panic!("Unexpectedly parsed the source \"{}\" as\n{:?} instead of\n{:?}", s, w, correct)
            },
            Err(err) => panic!("Failed to parse the source \"{}\": {}", s, err),
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
    send_and_sync::<Parser<::std::vec::IntoIter<Token>, builder::DefaultBuilder>>();
}
