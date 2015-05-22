# libshell
## A Rust library for parsing and running Unix shell commands

This library seeks to offer functionality for parsing and running shell commands
as defined by the
[POSIX.1-2008](http://pubs.opengroup.org/onlinepubs/9699919799/)
standard. Eventually it will work with external tokenizers and AST builders to
either use in place of the default implementation, or to extend the standard
grammar with custom definitions.

## Goals

* Provide an interface for parsing shell grammar
* Provide an interface for extending the default parser
* Provide several builtin shell utilities as defined by POSIX.1-2008

## Non-goals

* 100% POSIX.1-2008 compliance: the standard is used as a baseline for
implementation and features may be further added (or dropped) based on what
makes sense or is most useful
* Implement a full shell that will replace bash, zsh, ksh, or any other existing
shell: see the use cases below.

## Use cases

If shell scripts are of interest beyond simply running, this library allows you
to get to the meat of your project without having to write your own parser. If
you would ever like to extend the shell syntax, the only work that remains is
proportional to the syntax extensions.

Example projects:

* Extending the shell grammar with more expressive keywords or tokens, e.g. add
a forked-pipe token which pipes the output of one command to two or more
separate process
* Perform analysis on shell scripts: most used commands, unhandled situations,
lack of cleanup, etc.
* Optimize and compile shell scripts into native code to avoid shell runtime
overhead, or maybe even build the script into a library to be invoked from other
code
