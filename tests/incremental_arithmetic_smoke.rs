// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Smoke test for Stage 7 of the incremental-arithmetic plan: end-to-end
//! parity between `--arithmetic internal` (one-shot) and
//! `--arithmetic incremental` (persistent solver) on the LIA example files.
//!
//! Full differential coverage against the regression suite is Stage 8; this
//! test is a quick sanity check that the wiring in `main.rs` /
//! `cadical_propagator.rs` / `lialp::check_integer_constraints_satisfiable_incremental`
//! matches the one-shot path on inputs small enough to run under debug.

use std::fs;
use std::path::Path;
use std::process::Command;

#[test]
fn incremental_matches_internal_on_lia_examples() {
    let dir = Path::new("tests/lia_examples");
    let binary = env!("CARGO_BIN_EXE_sundance-smt");

    let mut checked = 0;
    for entry in fs::read_dir(dir).expect("read lia_examples") {
        let path = entry.unwrap().path();
        if path.extension().and_then(|s| s.to_str()) != Some("smt2") {
            continue;
        }
        checked += 1;

        let internal = run(binary, &path, "internal");
        let incremental = run(binary, &path, "incremental");
        assert_eq!(
            internal,
            incremental,
            "incremental disagreed with internal on {}: internal={internal:?}, incremental={incremental:?}",
            path.display()
        );
    }
    assert!(checked > 0, "expected at least one LIA example to run");
}

fn run(binary: &str, path: &Path, arithmetic: &str) -> String {
    let output = Command::new(binary)
        .args(["--arithmetic", arithmetic, path.to_str().unwrap()])
        .output()
        .expect("failed to run sundance-smt");
    assert!(
        output.status.success(),
        "sundance-smt exited non-zero on {} (--arithmetic {}): stderr={}",
        path.display(),
        arithmetic,
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8_lossy(&output.stdout).trim().to_string()
}
