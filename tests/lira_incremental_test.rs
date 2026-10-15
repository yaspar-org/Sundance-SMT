// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! End-to-end tests of the incremental internal arithmetic backend
//! (`--arithmetic internalincremental`), run on the release binary whatever arithmetic the CI
//! matrix row selects.

use std::path::Path;
use std::process::{Command, Stdio};
use std::thread;
use std::time::{Duration, Instant};

/// Run the solver on `file` with `--arithmetic internalincremental` plus `args`. Returns its
/// stdout and wall time, or `None` if it is still running after `limit` (it is then killed).
fn run(file: &str, args: &[&str], limit: Duration) -> Option<(String, Duration)> {
    let path = Path::new("tests/lira_incremental").join(file);
    let start = Instant::now();
    let mut child = Command::new(env!("CARGO_BIN_EXE_sundance-smt"))
        .arg(&path)
        .args(["--arithmetic", "internalincremental"])
        .args(args)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to start the solver");
    loop {
        if child
            .try_wait()
            .expect("failed to wait for the solver")
            .is_some()
        {
            let out = child
                .wait_with_output()
                .expect("failed to read the solver output");
            let stdout = String::from_utf8_lossy(&out.stdout).trim().to_string();
            return Some((stdout, start.elapsed()));
        }
        if start.elapsed() > limit {
            let _ = child.kill();
            let _ = child.wait();
            return None;
        }
        thread::sleep(Duration::from_millis(20));
    }
}

#[test]
fn div_mod_by_symbol_is_supported() {
    for file in ["div_mod_by_symbol.smt2", "div_by_uninterpreted_term.smt2"] {
        let (out, _) = run(file, &[], Duration::from_secs(30))
            .unwrap_or_else(|| panic!("{file}: no answer within 30 s"));
        assert_eq!(out, "unsat", "{file}");
    }
}

#[test]
fn opaque_div_never_answers_sat() {
    let (out, _) = run(
        "div_by_symbol_no_wrong_sat.smt2",
        &[],
        Duration::from_secs(30),
    )
    .expect("no answer within 30 s");
    assert!(
        out == "unknown" || out == "unsat",
        "expected unknown, got {out:?}"
    );
}

#[test]
fn branch_and_bound_respects_timeout() {
    let (out, elapsed) = run(
        "branch_and_bound_diverges.smt2",
        &["--timeout=2"],
        Duration::from_secs(30),
    )
    .expect("no answer within 30 s: --timeout=2 was not honored");
    assert!(
        out == "unknown" || out == "unsat",
        "expected unknown (or unsat), got {out:?}"
    );
    assert!(elapsed < Duration::from_secs(15), "took {elapsed:?}");
}
