// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::process::Command;

fn run_solver(goal_based: bool) -> (String, String) {
    let mut command = Command::new(env!("CARGO_BIN_EXE_sundance-smt"));
    command.args([
        "tests/goal_based_instantiation/order.smt2",
        "--arithmetic",
        "internal",
        "--debug",
        "22",
    ]);
    if goal_based {
        command.arg("--goal-based-instantiation");
    }
    let output = command.output().expect("failed to run sundance-smt");

    assert!(
        output.status.success(),
        "solver failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(String::from_utf8_lossy(&output.stdout).trim(), "unsat");
    (
        String::from_utf8(output.stdout).unwrap(),
        String::from_utf8(output.stderr).unwrap(),
    )
}

fn first_instantiation(stderr: &str) -> &str {
    stderr
        .lines()
        .find(|line| line.contains("We are adding the instantiation"))
        .expect("solver did not report an instantiation")
}

#[test]
fn materializes_the_goal_nearest_match_first() {
    let (_, stderr) = run_solver(true);
    let first_instantiation = first_instantiation(&stderr);
    assert!(
        first_instantiation.contains("(p a)") && first_instantiation.contains("(q a)"),
        "expected the a-instance first, got: {first_instantiation}"
    );
}

#[test]
fn disabled_mode_preserves_ematch_discovery_order() {
    let (_, stderr) = run_solver(false);
    let first_instantiation = first_instantiation(&stderr);
    assert!(
        first_instantiation.contains("(p b)") && first_instantiation.contains("(q b)"),
        "expected the b-instance first, got: {first_instantiation}"
    );
}
