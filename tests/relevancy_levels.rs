// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::path::Path;
use std::process::Command;

fn run_with_strict_relevancy(relative_path: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/regression/smt_files")
        .join(relative_path);
    let output = Command::new(env!("CARGO_BIN_EXE_sundance-smt"))
        .arg(path)
        .arg("--relevancy")
        .arg("2")
        .output()
        .expect("failed to run sundance-smt");

    assert!(
        output.status.success(),
        "solver failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout)
        .expect("solver output was not UTF-8")
        .trim()
        .to_owned()
}

#[test]
fn strict_relevancy_processes_datatype_generated_equalities() {
    assert_eq!(
        run_with_strict_relevancy("datatypes/tester-constructor3-reduced3.smt2"),
        "unsat"
    );
}

#[test]
fn strict_relevancy_processes_arithmetic_theory_atoms() {
    assert_eq!(
        run_with_strict_relevancy("arithmetic/nelsonoppen_advanced.smt2"),
        "unsat"
    );
}
