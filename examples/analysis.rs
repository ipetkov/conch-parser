//! An example of how one may analyze a shell program. In this case,
//! we traverse the parsed AST and count up how many times an "echo"
//! command appears in the source.

use conch_parser::ast;
use conch_parser::lexer::Lexer;
use conch_parser::parse::DefaultParser;
use owned_chars::OwnedCharsExt;

use std::io::{stdin, BufRead, BufReader};

fn main() -> Result<(), Box<dyn std::error::Error>> {
    let stdin = BufReader::new(stdin())
        .lines()
        .map(|result| result.expect("stdin error"))
        .flat_map(|mut line| {
            line.push('\n'); // BufRead::lines unfortunately strips \n and \r\n
            line.into_chars()
        });

    // Initialize our token lexer and shell parser with the program's input
    let lex = Lexer::new(stdin);
    let parser = DefaultParser::new(lex);

    let mut num_echo = 0usize;
    for cmd in parser {
        num_echo += count_echo_top_level(&cmd?);
    }

    println!("total number of echo commands: {}", num_echo);
    Ok(())
}

fn count_echo_top_level_array(cmds: &[ast::TopLevelCommand<String>]) -> usize {
    cmds.iter().map(count_echo_top_level).sum()
}

fn count_echo_top_level(cmd: &ast::TopLevelCommand<String>) -> usize {
    match &cmd.0 {
        ast::Command::Job(list) | ast::Command::List(list) => std::iter::once(&list.first)
            .chain(list.rest.iter().map(|and_or| match and_or {
                ast::AndOr::And(cmd) | ast::AndOr::Or(cmd) => cmd,
            }))
            .map(|cmd| count_echo_listable(&cmd))
            .sum(),
    }
}

fn count_echo_listable(cmd: &ast::DefaultListableCommand) -> usize {
    match cmd {
        ast::ListableCommand::Single(cmd) => count_echo_pipeable(cmd),
        ast::ListableCommand::Pipe(_, cmds) => cmds.into_iter().map(count_echo_pipeable).sum(),
    }
}

fn count_echo_pipeable(cmd: &ast::DefaultPipeableCommand) -> usize {
    match cmd {
        ast::PipeableCommand::Simple(cmd) => count_echo_simple(cmd),
        ast::PipeableCommand::Compound(cmd) => count_echo_compound(cmd),
        ast::PipeableCommand::FunctionDef(_, cmd) => count_echo_compound(cmd),
    }
}

fn count_echo_compound(cmd: &ast::DefaultCompoundCommand) -> usize {
    match &cmd.kind {
        ast::CompoundCommandKind::Brace(cmds) | ast::CompoundCommandKind::Subshell(cmds) => {
            count_echo_top_level_array(&cmds)
        }

        ast::CompoundCommandKind::While(lp) | ast::CompoundCommandKind::Until(lp) => {
            count_echo_top_level_array(&lp.guard) + count_echo_top_level_array(&lp.body)
        }

        ast::CompoundCommandKind::If {
            conditionals,
            else_branch,
        } => {
            let num_echo_in_conditionals = conditionals
                .iter()
                .map(|gbp| {
                    count_echo_top_level_array(&gbp.guard) + count_echo_top_level_array(&gbp.body)
                })
                .sum::<usize>();

            let num_echo_in_else = else_branch
                .as_ref()
                .map(|cmds| count_echo_top_level_array(&cmds))
                .unwrap_or(0);

            num_echo_in_conditionals + num_echo_in_else
        }

        ast::CompoundCommandKind::For { body, .. } => count_echo_top_level_array(&body),

        ast::CompoundCommandKind::Case { arms, .. } => arms
            .iter()
            .map(|pat| count_echo_top_level_array(&pat.body))
            .sum(),
    }
}

fn count_echo_simple(cmd: &ast::DefaultSimpleCommand) -> usize {
    cmd.redirects_or_cmd_words
        .iter()
        .filter_map(|redirect_or_word| match redirect_or_word {
            ast::RedirectOrCmdWord::CmdWord(w) => Some(&w.0),
            ast::RedirectOrCmdWord::Redirect(_) => None,
        })
        .filter_map(|word| match word {
            ast::ComplexWord::Single(w) => Some(w),
            // We're going to ignore concatenated words for simplicity here
            ast::ComplexWord::Concat(_) => None,
        })
        .filter_map(|word| match word {
            ast::Word::SingleQuoted(w) => Some(w),
            ast::Word::Simple(w) => get_simple_word_as_string(w),

            ast::Word::DoubleQuoted(words) if words.len() == 1 => {
                get_simple_word_as_string(&words[0])
            }
            ast::Word::DoubleQuoted(_) => None, // Ignore all multi-word double quoted strings
        })
        .filter(|w| *w == "echo")
        .count()
}

fn get_simple_word_as_string(word: &ast::DefaultSimpleWord) -> Option<&String> {
    match word {
        ast::SimpleWord::Literal(w) => Some(w),
        _ => None, // Ignoring substitutions and others for simplicity here
    }
}
