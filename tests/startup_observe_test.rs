// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Observing the CNF variables at startup must not call back into the propagator: CaDiCaL
//! notifies an observed variable that is already fixed at the root synchronously, from inside
//! `add_observed_var`, so the variables are observed before any clause can fix one. Every
//! propagator callback therefore happens during the solve, after "All clauses added, starting
//! solver".

use std::process::Command;

#[test]
fn no_propagator_callback_before_solve_with_unit_clause() {
    let dir = std::env::temp_dir().join(format!("sundance-startup-observe-{}", std::process::id()));
    std::fs::create_dir_all(&dir).unwrap();
    let input = dir.join("unit.smt2");
    std::fs::write(
        &input,
        "(declare-const p Bool)\n(declare-const q Bool)\n(assert p)\n(assert (or q (not p)))\n(check-sat)\n",
    )
    .unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_sundance-smt"))
        .arg(&input)
        .arg("--debug")
        .arg("2")
        .output()
        .expect("Failed to execute solver");
    let log = String::from_utf8_lossy(&output.stdout).to_string()
        + &String::from_utf8_lossy(&output.stderr);
    let start = log
        .find("All clauses added, starting solver")
        .expect("startup marker");
    let early = log[..start]
        .matches("PROPAGATOR: Processing assignments")
        .count();
    assert_eq!(
        early, 0,
        "{early} notify_assignment callback(s) ran before the solve started"
    );
    assert!(
        log[start..].contains("PROPAGATOR: Processing assignments"),
        "the root-fixed assignments are notified once the solve starts"
    );
    assert_eq!(
        String::from_utf8_lossy(&output.stdout)
            .lines()
            .last()
            .map(str::trim),
        Some("sat")
    );
}
