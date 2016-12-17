# conch-parser

[![Crates.io](https://img.shields.io/crates/v/conch-parser.svg)](https://crates.io/crates/conch-parser)
[![Documentation](https://docs.rs/conch-parser/badge.svg)](https://docs.rs/conch-parser)

A Rust library for parsing Unix shell commands.

## Quick Start
First, add this to your `Cargo.toml`:

```toml
[dependencies]
conch-parser = "0.1.0"
```

Next, you can get started with:

```rust
extern crate conch_parser;

use conch_parser::lexer::Lexer;
use conch_parser::parse::DefaultParser;

fn main() {
    // Initialize our token lexer and shell parser with the program's input
    let lex = Lexer::new("echo foo bar".chars());
    let parser = DefaultParser::new(lex);

    // Parse our input!
    for t in parser {
        println!("{:?}", t);
    }
}
```

## About
This library offers parsing shell commands as defined by the
[POSIX.1-2008][POSIX] standard. The parser remains agnostic to the final AST
representation by passing intermediate results to an AST `Builder`, allowing
for easy changes to the final AST structure without having to walk and transform
an entire AST produced by the parser. See the documentation for more information.

[POSIX]: http://pubs.opengroup.org/onlinepubs/9699919799/

### Goals
* Provide shell command parser which is correct and efficient, and agnostic to
the final AST representation
* Parsing should never require any form of runtime, thus no part of the source
should have to be executed or evaluated when parsing

### Non-goals
* 100% POSIX.1-2008 compliance: the standard is used as a baseline for
implementation and features may be further added (or dropped) based on what
makes sense or is most useful
* Feature parity with all major shells: unless a specific feature is
widely used (and considered common) or another compelling reason exists
for inclusion. However, this is not to say that the library will never
support extensions for adding additional syntax features.

## Supported grammar
- [x] Conditional lists (`foo && bar || baz`)
- [x] Pipelines (`! foo | bar`)
- [x] Compound commands
  - [x] Brace blocks (`{ foo; }`)
  - [x] Subshells (`$(foo)`)
  - [x] `for` / `case` / `if` / `while` / `until`
- [x] Function declarations
- [x] Redirections
- [x] Heredocs
- [x] Comments
- [x] Parameters (`$foo`, `$@`, etc.)
- [x] Parameter substitutions (`${foo:-bar}`)
- [x] Quoting (single, double, backticks, escaping)
- [ ] Arithmetic substitutions
  - [x] Common arithmetic operations required by the [standard][POSIX-arith]
  - [x] Variable expansion
  - [ ] Other inner abitrary parameter/substitution expansion

[POSIX-arith]: http://pubs.opengroup.org/onlinepubs/9699919799/utilities/V3_chap02.html#tag_18_06_04

## License
Licensed under either of

 * Apache License, Version 2.0, ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

### Contribution
Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the Apache-2.0
license, shall be dual licensed as above, without any additional terms or
conditions.
