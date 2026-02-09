// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! A file containting functions that may be useful elswhere

use std::collections::{BTreeMap, BTreeSet};

use yaspar_ir::ast::Term;

// For collections that need deterministic iteration, we use BTreeMap/BTreeSet
// These maintain sorted order naturally, so iteration is always deterministic
pub type DeterministicHashMap<K, V> = BTreeMap<K, V>;
pub type DeterministicHashSet<T> = BTreeSet<T>;

/// Global debug level - controls which debug messages are printed
pub static DEBUG_LEVEL: std::sync::atomic::AtomicU8 = std::sync::atomic::AtomicU8::new(0);

/// Debug macro -> used to print debug statements
#[macro_export]
macro_rules! debug_println {
    // Version with importance level and indentation
    ($importance:expr, $indent:expr, $($arg:tt)*) => {{
        let debug_level = $crate::utils::DEBUG_LEVEL.load(std::sync::atomic::Ordering::Relaxed);
        let importance: u8 = $importance;
        if importance >= debug_level {
            let indent: usize = $indent;
            let indent_str = "  ".repeat(indent);
            let color_str = match importance {
                0 => "\x1b[90m", // gray
                1 => "\x1b[34m", // blue
                2 => "\x1b[32m", // green
                3 => "\x1b[33m", // yellow
                4 => "\x1b[35m", // magenta
                5 => "\x1b[36m", // cyan
                _ => "\x1b[31m", // red
            };
            eprint!("{}{}", color_str, indent_str);
            eprintln!($($arg)*);
            eprint!("\x1b[0m");
        }
    }};

    // Backward compatibility - default importance 1, no indent
    ($($arg:tt)*) => {
        $crate:: debug_println!(1, 0, $($arg)*)
    };
}

// Takes in a List of terms and returns a String (useful for debugging)
pub fn fmt_termlist(terms: Vec<Term>) -> String {
    let mut term_string = String::new();

    for term in terms {
        term_string.push_str(&term.to_string());
        term_string.push_str(", ");
    }

    term_string
}
