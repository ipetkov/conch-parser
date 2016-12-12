//! A library for parsing programs written in the shell programming language.
//!
//! The `Parser` implementation will pass all of its intermediate parse results
//! to a `Builder` implementation, allowing the `Builder` to transform the
//! results to a desired format. This allows for customizing what AST is
//! produced without having to walk and transform an entire AST produced by
//! the parser.
//!
//! See the `Parser` documentation for more information on getting started.
//!
//! # Supported Grammar
//!
//! * Conditional lists (`foo && bar || baz`)
//! * Pipelines (`! foo | bar`)
//! * Compound commands
//!  * Brace blocks (`{ foo; }`)
//!  * Subshells (`$(foo)`)
//!  * `for` / `case` / `if` / `while` / `until`
//! * Function declarations
//! * Redirections
//! * Heredocs
//! * Comments
//! * Parameters (`$foo`, `$@`, etc.)
//! * Parameter substitutions (`${foo:-bar}`)
//! * Arithmetic substitutions
//!  * Common arithmetic operations required by the POSIX standard
//!  * Variable expansion
//!  * **Not yet implemented**: Other inner abitrary parameter/substitution expansion
//!
//! # Supported Cargo Features
//!
//! * `clippy`: compile with clippy lints enabled
//! * `nightly`: enable unstable features/optimizations which require a nightly compiler

#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]

#![cfg_attr(all(not(test), feature = "clippy"), deny(print_stdout))]
#![cfg_attr(feature = "clippy", deny(wrong_self_convention))]

#![deny(missing_copy_implementations)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(trivial_casts)]
#![deny(trivial_numeric_casts)]
#![deny(unused_import_braces)]
#![deny(unused_qualifications)]

#![forbid(unsafe_code)]

// Nightly optimizations that don't need their own feature
#![cfg_attr(feature = "nightly", feature(fused))]

macro_rules! if_nightly {
    ($($i:item)*) => ($(
        #[cfg(feature = "nightly")]
        $i
    )*)
}

extern crate void;

pub mod ast;
pub mod lexer;
pub mod parse;
pub mod token;
