// SPDX-License-Identifier: GPL-2.0

//! Generates KUnit tests from saved `rustdoc`-generated tests.
//!
//! KUnit passes a context (`struct kunit *`) to each test, which should be forwarded to the other
//! KUnit functions and macros.
//!
//! However, we want to keep this as an implementation detail because:
//!
//!   - Test code should not care about the implementation.
//!
//!   - Documentation looks worse if it needs to carry extra details unrelated to the piece
//!     being described.
//!
//!   - Test code should be able to define functions and call them, without having to carry
//!     the context.
//!
//!   - Later on, we may want to be able to test non-kernel code (e.g. `core`, `alloc` or
//!     third-party crates) which likely use the standard library `assert*!` macros.
//!
//! For this reason, instead of the passed context, `kunit_get_current_test()` is used instead
//! (i.e. `current->kunit_test`).
//!
//! Note that this means other threads/tasks potentially spawned by a given test, if failing, will
//! report the failure in the kernel log but will not fail the actual test. Saving the pointer in
//! e.g. a `static` per test does not fully solve the issue either, because currently KUnit does
//! not support assertions (only expectations) from other tasks. Thus leave that feature for
//! the future, which simplifies the code here too. We could also simply not allow `assert`s in
//! other tasks, but that seems overly constraining, and we do want to support them, eventually.

use std::io::{BufWriter, Read, Write};
use std::{fs, fs::File};

fn main() {
    let mut paths = fs::read_dir("rust/test/doctests/kernel")
        .unwrap()
        .map(|entry| entry.unwrap().path())
        .collect::<Vec<_>>();

    // Sort paths for clarity.
    paths.sort();

    let mut rust_tests = String::new();
    let mut c_test_declarations = String::new();
    let mut c_test_cases = String::new();
    let mut body = String::new();
    let mut last_file = String::new();
    let mut number = 0;
    for path in paths {
        // The `name` follows the `{file}_{line}_{number}` pattern (see description in
        // `scripts/rustdoc_test_builder.rs`). Discard the `number`.
        let name = path.file_name().unwrap().to_str().unwrap().to_string();

        // Extract the `file` and the `line`, discarding the `number`.
        let (file, line) = name.rsplit_once('_').unwrap().0.rsplit_once('_').unwrap();

        // Generate an ID sequence ("test number") for each one in the file.
        if file == last_file {
            number += 1;
        } else {
            number = 0;
            last_file = file.to_string();
        }

        // Generate a KUnit name (i.e. test name and C symbol) for this test.
        //
        // We avoid the line number, like `rustdoc` does, to make things slightly more stable for
        // bisection purposes. However, to aid developers in mapping back what test failed, we will
        // print a diagnostics line in the KTAP report.
        let kunit_name = format!("rust_doctest_kernel_{file}_{number}");

        // Read the test's text contents to dump it below.
        body.clear();
        File::open(path).unwrap().read_to_string(&mut body).unwrap();

        let line = line.parse::<core::ffi::c_int>().unwrap();

        use std::fmt::Write;
        write!(
            rust_tests,
            r#"/// Generated `{name}` KUnit test case from a Rust documentation test.
#[no_mangle]
pub extern "C" fn {kunit_name}(__kunit_test: *mut kernel::bindings::kunit) {{
    /// Overrides the usual [`assert!`] macro with one that calls KUnit instead.
    #[allow(unused)]
    macro_rules! assert {{
        ($cond:expr $(,)?) => {{{{
            kernel::kunit_assert!("{kunit_name}", $cond);
        }}}}
    }}

    /// Overrides the usual [`assert_eq!`] macro with one that calls KUnit instead.
    #[allow(unused)]
    macro_rules! assert_eq {{
        ($left:expr, $right:expr $(,)?) => {{{{
            kernel::kunit_assert_eq!("{kunit_name}", $left, $right);
        }}}}
    }}

    // Many tests need the prelude, so provide it by default.
    #[allow(unused)]
    use kernel::prelude::*;

    // Display line number so that developers can map the test easily to the source code.
    kernel::kunit::info(format_args!("    # Doctest from line {line}\n"));

    {{
        {body}
        main();
    }}
}}

"#
        )
        .unwrap();

        write!(c_test_declarations, "void {kunit_name}(struct kunit *);\n").unwrap();
        write!(c_test_cases, "    KUNIT_CASE({kunit_name}),\n").unwrap();
    }

    let rust_tests = rust_tests.trim();
    let c_test_declarations = c_test_declarations.trim();
    let c_test_cases = c_test_cases.trim();

    write!(
        BufWriter::new(File::create("rust/doctests_kernel_generated.rs").unwrap()),
        r#"//! `kernel` crate documentation tests.

const __LOG_PREFIX: &[u8] = b"rust_doctests_kernel\0";

{rust_tests}
"#
    )
    .unwrap();

    write!(
        BufWriter::new(File::create("rust/doctests_kernel_generated_kunit.c").unwrap()),
        r#"/*
 * `kernel` crate documentation tests.
 */

#include <kunit/test.h>

{c_test_declarations}

static struct kunit_case test_cases[] = {{
    {c_test_cases}
    {{ }}
}};

static struct kunit_suite test_suite = {{
    .name = "rust_doctests_kernel",
    .test_cases = test_cases,
}};

kunit_test_suite(test_suite);

MODULE_LICENSE("GPL");
"#
    )
    .unwrap();
}
