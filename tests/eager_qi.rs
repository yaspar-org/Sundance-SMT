// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::path::Path;
use std::process::Command;

fn run_eager_qi(file: &str) -> String {
    let path = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/eager_qi")
        .join(file);
    let output = Command::new(env!("CARGO_BIN_EXE_sundance-smt"))
        .arg(path)
        .arg("--eager-qi")
        .arg("1")
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
fn eager_instantiation_can_refute_before_the_final_round() {
    assert_eq!(
        run_eager_qi("eager_instantiation_before_model.smt2"),
        "unsat"
    );
}

#[test]
fn final_round_is_not_limited_by_eager_generation_cap() {
    assert_eq!(run_eager_qi("eager_generation_fallback.smt2"), "unsat");
}
