//! Defines abstract representations of the shell source.
use std::fmt::{Display, Formatter, Result};

pub mod builder;
pub use syntax::ast::builder::{Builder, CommandBuilder};

/// Represents reading a parameter (or variable) value, e.g. `$foo`.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Parameter {
    /// $@
    At,
    /// $*
    Star,
    /// $#
    Pound,
    /// $?
    Question,
    /// $-
    Dash,
    /// $$
    Dollar,
    /// $!
    Bang,
    /// $0, $1, ..., $9, ${100}
    Positional(u32),
    /// $foo
    Var(String),
    /// $(cmd)
    CommandSubst(Command),
}

/// Represents whitespace delimited text.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Word {
    /// A non-special literal word.
    Literal(String),
    /// Several distinct words concatenated together.
    Concat(Vec<Word>),
    /// List of words concatenated within single quotes. Virtually
    /// identical to `Literal`, but makes the distinction if needed.
    SingleQuoted(String),
    /// List of words concatenated within double quotes.
    DoubleQuoted(Vec<Word>),
    /// Access of a value inside a parameter, e.g. `$foo` or `$$`.
    Param(Parameter),
    /// A token which normally has a special meaning is treated as a literal
    /// because it was escaped, typically with a backslash, e.g. `\"`.
    Escaped(String),
    /// Represents `*`, useful for handling pattern expansions.
    Star,
    /// Represents `?`, useful for handling pattern expansions.
    Question,
    /// Represents `~`, useful for handling tilde expansions.
    Tilde,
}

/// Represents redirecting a command's file descriptors.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Redirect {
    /// Open a file for reading, e.g. [n]< file
    Read(Option<Word>, Word),
    /// Open a file for writing after truncating, e.g. [n]> file
    Write(Option<Word>, Word),
    /// Open a file for reading and writing, e.g. [n]<> file
    ReadWrite(Option<Word>, Word),
    /// Open a file for writing, appending to the end, e.g. [n]>> file
    Append(Option<Word>, Word),
    /// Open a file for writing, failing if the `noclobber` shell option is set, e.g.[n]>| file
    Clobber(Option<Word>, Word),

    /// Duplicate a file descriptor for reading, e.g. [n]<& n
    DupRead(Option<Word>, Word),
    /// Duplicate a file descriptor for writing, e.g. [n]>& n
    DupWrite(Option<Word>, Word),

    /// Close a file descriptor for reading, e.g. [n]<&-
    CloseRead(Option<Word>),
    /// Close a file descriptor for writing, e.g. [n]>&-
    CloseWrite(Option<Word>),
}

/// Represents a parsed newline, more specifically, the presense of a comment
/// immediately preceeding the newline.
///
/// Since shell comments are usually treated as a newline, they can be present
/// anywhere a newline can be as well. Thus if it is desired to retain comments
/// they can be optionally attached to a parsed newline.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Newline(pub Option<String>);

/// Represents any valid shell command.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Command {
    /// A compound command which runs the second if the first succeeds,
    /// e.g. `foo && bar`.
    And(Box<Command>, Box<Command>),
    /// A compound command which runs the second if the first fails,
    /// e.g. `foo || bar`.
    Or(Box<Command>, Box<Command>),
    /// A chain of concurrent commands where the standard output of the
    /// previous becomes the standard input of the next, e.g.
    /// `[!] foo | bar | baz`.
    ///
    /// The bool indicates if a logical negation of the last command's status
    /// should be returned.
    Pipe(bool, Vec<Command>),
    /// A command that runs asynchronously, that is, the shell will not wait
    /// for it to exit before running the next command, e.g. `foo &`.
    Job(Box<Command>),
    /// A class of commands where redirection is applied to a command group.
    Compound(Box<CompoundCommand>, Vec<Redirect>),
    /// A function declaration, associating a name with a group of commands,
    /// e.g. `function foo() { echo foo function; }`.
    Function(String, Box<Command>),
    /// The simplest possible command: an executable with arguments,
    /// environment variable assignments, and redirections.
    Simple(Box<SimpleCommand>),
}

/// A class of commands where redirection is applied to a command group.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum CompoundCommand {
    /// A group of commands that should be executed in the current environment.
    Brace(Vec<Command>),
    /// A group of commands that should be executed in a subshell environment.
    Subshell(Vec<Command>),
    /// A command that executes its body as long as its guard exits successfully.
    ///
    /// Variant structure: `While(guard, body)`.
    While(Vec<Command>, Vec<Command>),
    /// A command that executes its body as until as its guard exits unsuccessfully.
    ///
    /// Variant structure: `Until(guard, body)`.
    Until(Vec<Command>, Vec<Command>),
    /// A conditional command that runs the respective command branch when a
    /// certain of the first condition that exits successfully.
    ///
    /// Variant structure: `If( (guard, branch)+, else_branch )`.
    If(Vec<(Vec<Command>, Vec<Command>)>, Option<Vec<Command>>),
    /// A command that binds a variable to a number of provided words and runs
    /// its body once for each binding.
    ///
    /// Variant structure: `For(var_name, words, body)`.
    For(String, Option<Vec<Word>>, Vec<Command>),
    /// A command that behaves much like a `match` statment in Rust, running
    /// a branch of commands if a specified word matches another literal or
    /// glob pattern.
    ///
    /// Variant structure: `Case( to_match, (pattern_alternative+, commands*)* )`
    Case(Word, Vec<(Vec<Word>, Vec<Command>)>),
}

/// The simplest possible command: an executable with arguments,
/// environment variable assignments, and redirections.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct SimpleCommand {
    /// Name or path of the executable. It's possible to have to have a
    /// command that is only an assigment which would set a value in the
    /// global environment, making the executable optional.
    pub cmd: Option<Word>,
    /// Arguments supplied to the executable.
    pub args: Vec<Word>,
    /// Environment variable assignments for this command, bound as
    /// tuples of (var name, value).
    pub vars: Vec<(String, Option<Word>)>,
    /// All redirections that should be applied before running the command.
    pub io: Vec<Redirect>,
}

impl Display for Parameter {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use self::Parameter::*;

        match *self {
            At       => fmt.write_str("$@"),
            Star     => fmt.write_str("$*"),
            Pound    => fmt.write_str("$#"),
            Question => fmt.write_str("$?"),
            Dash     => fmt.write_str("$-"),
            Dollar   => fmt.write_str("$$"),
            Bang     => fmt.write_str("$!"),

            Var(ref p)    => write!(fmt, "${{{}}}", p),
            Positional(p) => if p <= 9 {
                write!(fmt, "${}", p)
            } else {
                write!(fmt, "${{{}}}", p)
            },

            CommandSubst(ref c) => write!(fmt, "$({})", c),
        }
    }
}

impl Display for Word {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use self::Word::*;

        match *self {
            Star           => fmt.write_str("*"),
            Question       => fmt.write_str("?"),
            Tilde          => fmt.write_str("~"),
            Literal(ref s) => fmt.write_str(s),

            Param(ref p)        => write!(fmt, "{}", p),
            Escaped(ref s)      => write!(fmt, "\\{}", s),
            SingleQuoted(ref w) => write!(fmt, "'{}'", w),

            DoubleQuoted(ref words) => {
                try!(fmt.write_str("\""));
                for w in words { try!(write!(fmt, "{}", w)); }
                fmt.write_str("\"")
            },

            Concat(ref words) => {
                for w in words {
                    try!(write!(fmt, "{}", w));
                }

                Ok(())
            },
        }
    }
}

impl Display for Redirect {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use self::Redirect::*;
        match *self {
            Read(Some(ref fd), ref p)      => write!(fmt, "{}<{}",  fd, p),
            Write(Some(ref fd), ref p)     => write!(fmt, "{}>{}",  fd, p),
            ReadWrite(Some(ref fd), ref p) => write!(fmt, "{}<>{}", fd, p),
            Append(Some(ref fd), ref p)    => write!(fmt, "{}>>{}", fd, p),
            Clobber(Some(ref fd), ref p)   => write!(fmt, "{}>|{}", fd, p),
            DupRead(Some(ref fd), ref p)   => write!(fmt, "{}<&{}", fd, p),
            DupWrite(Some(ref fd), ref p)  => write!(fmt, "{}>&{}", fd, p),

            CloseRead(Some(ref fd))  => write!(fmt, "{}<&-", fd),
            CloseWrite(Some(ref fd)) => write!(fmt, "{}>&-", fd),

            Read(None, ref p)      => write!(fmt, "<{}",  p),
            Write(None, ref p)     => write!(fmt, ">{}",  p),
            ReadWrite(None, ref p) => write!(fmt, "<>{}", p),
            Append(None, ref p)    => write!(fmt, ">>{}", p),
            Clobber(None, ref p)   => write!(fmt, ">|{}", p),
            DupRead(None, ref p)   => write!(fmt, "<&{}", p),
            DupWrite(None, ref p)  => write!(fmt, ">&{}", p),

            CloseRead(None)  => fmt.write_str("<&-"),
            CloseWrite(None) => fmt.write_str(">&-"),
        }
    }
}

impl Display for Newline {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        match self.0 {
            Some(ref s) => write!(fmt, "{}\n", s),
            None => write!(fmt, "\n"),
        }
    }
}

struct CmdVec<'a>(&'a Vec<Command>);
impl<'a> Display for CmdVec<'a> {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        let mut iter = self.0.iter();
        if let Some(c) = iter.next() {
            if let &Command::Job(_) = c {
                try!(write!(fmt, "{}", c))
            } else {
                try!(write!(fmt, "{};", c))
            }
        }

        for c in iter {
            if let &Command::Job(_) = c {
                try!(write!(fmt, " {}", c))
            } else {
                try!(write!(fmt, " {};", c))
            }
        }

        Ok(())
    }
}

struct RedirVec<'a>(&'a Vec<Redirect>);
impl<'a> Display for RedirVec<'a> {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        if self.0.is_empty() { return Ok(()) }

        let mut iter = self.0.iter();
        if let Some(r) = iter.next() {
            try!(write!(fmt, "{}", r));
        }

        for r in iter {
            try!(write!(fmt, " {}", r));
        }

        Ok(())
    }
}

impl Display for Command {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use self::Command::*;
        match *self {
            And(ref a, ref b) => write!(fmt, "{} && {}", a, b),
            Or(ref a, ref b)  => write!(fmt, "{} || {}", a, b),

            Pipe(bang, ref cmds) => {
                if bang { try!(fmt.write_str("! ")) }
                let mut iter = cmds.into_iter();
                match iter.next() {
                    Some(first) => try!(write!(fmt, "{}", first)),
                    None => return Ok(()),
                }

                for c in iter {
                    try!(write!(fmt, " | {}", c));
                }

                Ok(())
            },

            Job(ref c) => write!(fmt, "{} &", c),
            Compound(ref c, ref io) => write!(fmt, "{} {}", c, RedirVec(io)),
            Function(ref name, ref body) => write!(fmt, "function {}() {}", name, body),
            Simple(ref c) => write!(fmt, "{}", c),
        }
    }
}

impl Display for CompoundCommand {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        use self::CompoundCommand::*;
        match *self {
            Brace(ref cmds) => write!(fmt, "{{ {} }}", CmdVec(cmds)),
            Subshell(ref cmds) => write!(fmt, "({})", CmdVec(cmds)),
            While(ref guard, ref body) => write!(fmt, "while {} do {} done", CmdVec(guard), CmdVec(body)),
            Until(ref guard, ref body) => write!(fmt, "until {} do {} done", CmdVec(guard), CmdVec(body)),

            If(ref branches, ref els) => {
                let mut iter = branches.iter();
                match iter.next() {
                    Some(&(ref guard, ref body)) => try!(write!(fmt, "if {} then {}", CmdVec(guard), CmdVec(body))),
                    None => return Ok(()),
                }

                for &(ref guard, ref body) in iter {
                    try!(write!(fmt, " elif {} then {}", CmdVec(guard), CmdVec(body)))
                }

                if let &Some(ref cmds) = els {
                    try!(write!(fmt, " else {}", CmdVec(cmds)))
                }

                fmt.write_str(" fi")
            },

            For(ref name, ref words, ref body) => {
                try!(write!(fmt, "for {}", name));
                if let &Some(ref words) = words {
                    try!(fmt.write_str(" in"));
                    for w in words {
                        try!(write!(fmt, " {}", w));
                    }
                    try!(fmt.write_str(";"));
                }

                write!(fmt, " do {} done", CmdVec(body))
            },

            Case(ref word, ref arms) => {
                try!(write!(fmt, "case {} in", word));

                for &(ref pats, ref cmds) in arms {
                    let mut pat_iter = pats.iter();
                    if let Some(p) = pat_iter.next() {
                        try!(write!(fmt, " {}", p))
                    }

                    for p in pat_iter {
                        try!(write!(fmt, " | {}", p))
                    }

                    try!(write!(fmt, ") {} ;;", CmdVec(cmds)))
                }

                fmt.write_str(" esac")
            },
        }
    }
}

impl Display for SimpleCommand {
    fn fmt(&self, fmt: &mut Formatter) -> Result {
        let mut var_iter = self.vars.iter();
        if let Some(&(ref var, ref val)) = var_iter.next() {
            match val {
                &Some(ref val) => try!(write!(fmt, "{}={}", var, val)),
                &None          => try!(write!(fmt, "{}=", var)),
            }
        }

        for &(ref var, ref val) in var_iter {
            match val {
                &Some(ref val) => try!(write!(fmt, " {}={}", var, val)),
                &None          => try!(write!(fmt, " {}=", var)),
            }
        }

        if !self.vars.is_empty() && self.cmd.is_some() {
            try!(fmt.write_str(" "));
        }

        if let Some(ref cmd) = self.cmd {
            try!(write!(fmt, "{}", cmd));
            for arg in self.args.iter() {
                try!(write!(fmt, " {}", arg));
            }
        }

        if !self.vars.is_empty() || self.cmd.is_some() {
            try!(fmt.write_str(" "));
        }

        write!(fmt, "{}", RedirVec(&self.io))
    }
}

#[cfg(test)]
mod test {
    use syntax::ast::*;
    use syntax::parse::test as parse_test;
    use syntax::parse::test::make_parser;

    fn sample_simple_command() -> Command {
        let (cmd, args, vars, io) = parse_test::sample_simple_command();
        Command::Simple(Box::new(SimpleCommand { cmd: cmd, args: args, vars: vars, io: io }))
    }

    #[test]
    fn test_display_simple_command() {
        let cmd = Some(Word::Literal(String::from("foo")));
        let args = vec!(
            Word::Literal(String::from("bar")),
            Word::Literal(String::from("baz")),
        );
        let vars = vec!(
            (String::from("FOO"), Some(Word::Literal(String::from("value")))),
            (String::from("BAR"), None),
        );
        let io = vec!(
            Redirect::Write(
                Some(Word::Concat(vec!(
                    Word::Literal(String::from("123")),
                    Word::Param(Parameter::Dollar),
                ))),
                Word::Literal(String::from("out")),
            ),
            Redirect::CloseWrite(Some(Word::SingleQuoted(String::from("1")))),
        );

        let cmds = vec!(
            SimpleCommand { cmd: cmd.clone(),  args: args.clone(), vars: vars.clone(), io: io.clone() },
            SimpleCommand { cmd: cmd.clone(),  args: args.clone(), vars: vars.clone(), io: vec!()     },
            SimpleCommand { cmd: cmd.clone(),  args: args.clone(), vars: vec!(),       io: io.clone() },
            SimpleCommand { cmd: cmd.clone(),  args: args.clone(), vars: vec!(),       io: vec!()     },
            SimpleCommand { cmd: cmd.clone(),  args: vec!(),       vars: vars.clone(), io: io.clone() },
            SimpleCommand { cmd: cmd.clone(),  args: vec!(),       vars: vars.clone(), io: vec!()     },
            SimpleCommand { cmd: cmd.clone(),  args: vec!(),       vars: vec!(),       io: io.clone() },
            SimpleCommand { cmd: cmd.clone(),  args: vec!(),       vars: vec!(),       io: vec!()     },
            SimpleCommand { cmd: None,         args: vec!(),       vars: vars.clone(), io: io.clone() },
            SimpleCommand { cmd: None,         args: vec!(),       vars: vars.clone(), io: vec!()     },
            SimpleCommand { cmd: None,         args: vec!(),       vars: vec!(),       io: io.clone() },
        );

        for c in cmds {
            let src = c.to_string();
            let correct = Command::Simple(Box::new(c));

            let parsed = match make_parser(&src).simple_command() {
                Ok(p) => p,
                Err(e) => panic!("The source \"{}\" generated from the command `{:#?}` failed to parse: {}", src, correct, e),
            };

            if correct != parsed {
                panic!("The source \"{}\" generated from the command `{:#?}` was parsed as `{:#?}`", src, correct, parsed);
            }
        }
    }

    #[test]
    fn test_display_compound_command() {
        use super::CompoundCommand::*;

        let sample = sample_simple_command();
        let two_samples = vec!(sample.clone(), sample.clone());

        let word_foo = Word::Literal(String::from("foo"));
        let word_bar = Word::Literal(String::from("bar"));

        let cmds = vec!(
            Brace(two_samples.clone()),
            Subshell(two_samples.clone()),
            While(two_samples.clone(), two_samples.clone()),
            Until(two_samples.clone(), two_samples.clone()),
            If(vec!((vec!(sample.clone()), two_samples.clone()), (vec!(sample.clone()), two_samples.clone())),
                Some(vec!(sample.clone())),
            ),
            If(vec!((vec!(sample.clone()), two_samples.clone()), (vec!(sample.clone()), two_samples.clone())), None),
            If(vec!((two_samples.clone(),  two_samples.clone())), Some(two_samples.clone())),
            If(vec!((two_samples.clone(),  two_samples.clone())), None),
            For(String::from("foo"), Some(vec!(word_foo.clone(), word_bar.clone())), two_samples.clone()),
            For(String::from("foo"), None, two_samples.clone()),
            Case(word_foo.clone(), vec!(
                    (vec!(word_foo.clone()),                   two_samples.clone()),
                    (vec!(word_foo.clone(), word_foo.clone()), vec!(sample.clone())),
            )),
            Case(word_foo.clone(), vec!(
                    (vec!(word_foo.clone()),                   vec!()),
                    (vec!(word_foo.clone(), word_foo.clone()), vec!()),
            )),
            Case(word_foo.clone(), vec!()),
        );

        for c in cmds {
            let src = c.to_string();
            let correct = Command::Compound(Box::new(c), vec!());

            let parsed = match make_parser(&src).compound_command() {
                Ok(p) => p,
                Err(e) => panic!("The source \"{}\" generated from the command `{:#?}` failed to parse: {}", src, correct, e),
            };

            if correct != parsed {
                panic!("The source \"{}\" generated from the command `{:#?}` was parsed as `{:#?}`", src, correct, parsed);
            }
        }
    }

    #[test]
    fn test_display_command() {
        use super::Command::*;

        let sample = sample_simple_command();
        let two_samples = vec!(sample.clone(), sample.clone());

        let io = vec!(
            Redirect::Write(
                Some(Word::Concat(vec!(
                    Word::Literal(String::from("123")),
                    Word::Param(Parameter::Dollar),
                ))),
                Word::Literal(String::from("out")),
            ),
            Redirect::CloseWrite(Some(Word::SingleQuoted(String::from("1")))),
        );

        let cmds = vec!(
            And(Box::new(sample.clone()), Box::new(sample.clone())),
            Or(Box::new(sample.clone()), Box::new(sample.clone())),
            Pipe(true,  two_samples.clone()),
            Pipe(false, two_samples.clone()),
            Job(Box::new(sample.clone())),
            Compound(Box::new(CompoundCommand::Brace(two_samples.clone())), io),
            Compound(Box::new(CompoundCommand::Brace(two_samples.clone())), vec!()),
            Function(String::from("foo"), Box::new(sample.clone())),
            sample,
        );

        for c in cmds {
            let src = c.to_string();

            let parsed = match make_parser(&src).complete_command() {
                Ok(Some(p)) => p,
                Ok(None) => panic!("The source \"{}\" generated from the command `{:#?}` failed to parse as anything", src, c),
                Err(e) => panic!("The source \"{}\" generated from the command `{:#?}` failed to parse: {}", src, c, e),
            };

            if c != parsed {
                panic!("The source \"{}\" generated from the command `{:#?}` was parsed as `{:#?}`", src, c, parsed);
            }
        }
    }

    #[test]
    fn test_display_parameter() {
        use super::Parameter::*;

        let params = vec!(
            At,
            Star,
            Pound,
            Question,
            Dash,
            Dollar,
            Bang,
            Positional(0),
            Positional(10),
            Positional(100),
            Var(String::from("foo_bar123")),
        );

        for p in params {
            let src = p.to_string();
            let correct = Word::Param(p);

            let parsed = match make_parser(&src).word() {
                Ok(Some(w)) => w,
                Ok(None) => panic!("The source \"{}\" generated from the command `{:#?}` failed to parse as anything", src, correct),
                Err(e) => panic!("The source \"{}\" generated from the command `{:#?}` failed to parse: {}", src, correct, e),
            };

            if correct != parsed {
                panic!("The source \"{}\" generated from the command `{:#?}` was parsed as `{:#?}`", src, correct, parsed);
            }
        }
    }

    #[test]
    fn test_display_newline() {
        let newlines = vec!(
            Newline(Some(String::from("#comment"))),
            Newline(None)
        );

        for n in newlines {
            let src = n.to_string();

            let parsed = match make_parser(&src).newline() {
                Some(n) => n,
                None => panic!("The source \"{}\" generated from `{:#?}` failed to parse as anything", src, n),
            };

            if n != parsed {
                panic!("The source \"{}\" generated from `{:#?}` was parsed as `{:#?}`", src, n, parsed);
            }
        }
    }

    #[test]
    fn test_display_word() {
        use super::Word::*;

        let words = vec!(
            Literal(String::from("foo")),
            Escaped(String::from(";")),
            Escaped(String::from(">")),
            Escaped(String::from("&")),
            Escaped(String::from("'")),
            Escaped(String::from("\"")),
            Concat(vec!(
                Literal(String::from("foo")),
                SingleQuoted(String::from("bar")),
                Param(Parameter::Var(String::from("foo_bar123"))),
                Star,
            )),
            SingleQuoted(String::from("bar\"\\\"")),
            DoubleQuoted(vec!(
                Literal(String::from("\n\nfoo\n")),
                Param(Parameter::Var(String::from("foo_bar123"))),
                Literal(String::from("'")),
                Escaped(String::from("$")),
                Escaped(String::from("`")),
                Escaped(String::from("\"")),
                Escaped(String::from("\\")),
                Escaped(String::from("\n")),
            )),
            Param(Parameter::At),
            Param(Parameter::Positional(0)),
            Param(Parameter::Positional(10)),
            Param(Parameter::Positional(100)),
            Param(Parameter::Var(String::from("foo_bar123"))),
            Star,
            Question,
            Tilde,
        );

        for w in words {
            let src = w.to_string();

            let parsed = match make_parser(&src).word() {
                Ok(Some(w)) => w,
                Ok(None) => panic!("The source \"{}\" generated from `{:#?}` failed to parse as anything", src, w),
                Err(e) => panic!("The source \"{}\" generated from `{:#?}` failed to parse: {}", src, w, e),
            };

            if w != parsed {
                panic!("The source \"{}\" generated from `{:#?}` was parsed as `{:#?}`", src, w, parsed);
            }
        }
    }

    #[test]
    fn test_display_redirect() {
        use super::Redirect::*;

        let path   = Word::Literal(String::from("foo"));
        let out_fd = Word::Literal(String::from("3"));
        let in_fd  = Word::Literal(String::from("2"));

        let redirects = vec!(
            Read(Some(in_fd.clone()), path.clone()),
            Write(Some(in_fd.clone()), path.clone()),
            ReadWrite(Some(in_fd.clone()), path.clone()),
            Append(Some(in_fd.clone()), path.clone()),
            Clobber(Some(in_fd.clone()), path.clone()),
            DupRead(Some(in_fd.clone()), out_fd.clone()),
            DupWrite(Some(in_fd.clone()), out_fd.clone()),
            CloseRead(Some(in_fd.clone())),
            CloseWrite(Some(in_fd.clone())),

            Read(None, path.clone()),
            Write(None, path.clone()),
            ReadWrite(None, path.clone()),
            Append(None, path.clone()),
            Clobber(None, path.clone()),
            DupRead(None, out_fd.clone()),
            DupWrite(None, out_fd.clone()),
            CloseRead(None),
            CloseWrite(None),
        );

        for r in redirects {
            let src = r.to_string();

            let parsed = match make_parser(&src).redirect() {
                Ok(Some(Ok(r))) => r,
                Ok(Some(Err(w))) => panic!("The source \"{}\" generated from `{:#?}` parsed as a word: {:#?}", src, r, w),
                Ok(None) => panic!("The source \"{}\" generated from `{:#?}` failed to parse as anything", src, r),
                Err(e) => panic!("The source \"{}\" generated from `{:#?}` failed to parse: {}", src, r, e),
            };

            if r != parsed {
                panic!("The source \"{}\" generated from `{:#?}` was parsed as `{:#?}`", src, r, parsed);
            }
        }
    }
}
