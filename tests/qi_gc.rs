// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::path::Path;
use std::process::Command;

#[test]
fn activation_literal_is_not_replayed_as_a_theory_assignment() {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/qi_gc")
        .join("activation_replay_without_relevancy.smt2");
    let output = Command::new(env!("CARGO_BIN_EXE_sundance-smt"))
        .arg(path)
        .arg("--qi-gc")
        .arg("--relevancy")
        .arg("false")
        .output()
        .expect("failed to run sundance-smt");

    assert!(
        output.status.success(),
        "solver failed:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(
        String::from_utf8(output.stdout)
            .expect("solver output was not UTF-8")
            .trim(),
        "unsat"
    );
}
