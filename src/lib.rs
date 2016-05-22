//! A library for parsing, executing, and analyzing programs
//! written in the shell programming language.
#![cfg_attr(feature = "clippy", feature(plugin))]
#![cfg_attr(feature = "clippy", plugin(clippy))]

#![cfg_attr(all(not(test), feature = "clippy"), deny(print_stdout))]
#![cfg_attr(feature = "clippy", deny(wrong_self_convention))]

#![deny(missing_copy_implementations)]
#![deny(missing_debug_implementations)]
#![deny(missing_docs)]
#![deny(trivial_casts)]
#![deny(unused_import_braces)]
#![deny(unused_qualifications)]

#![cfg_attr(feature = "runtime", feature(zero_one))]
#![cfg_attr(all(windows, feature = "runtime"), feature(unique))]

// Windows only libs
#[cfg(all(windows, feature = "runtime"))] extern crate kernel32;
#[cfg(all(windows, feature = "runtime"))] extern crate winapi;

#[cfg(feature = "runtime")] extern crate glob;
#[cfg(feature = "runtime")] extern crate libc;
#[cfg(feature = "runtime")] extern crate void;

/// Poor man's mktmp. A macro for creating "unique" test directories.
#[cfg(test)]
macro_rules! mktmp {
    () => {{
        let path = concat!("test-", module_path!(), "-", line!(), "-", column!());
        if cfg!(windows) {
            TempDir::new(&path.replace(":", "_")).unwrap()
        } else {
            TempDir::new(path).unwrap()
        }
    }};
}

#[cfg(feature = "runtime")]
pub mod runtime;
pub mod syntax;
