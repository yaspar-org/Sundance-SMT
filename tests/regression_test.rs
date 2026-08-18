// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::Path;
use std::process::{Child, Command};
use std::thread;
use std::time::Duration;

fn run_with_stats(query: &str, eager_qi: i64) -> (String, serde_json::Value) {
    let output = Command::new(env!("CARGO_BIN_EXE_sundance-smt"))
        .arg(query)
        .arg("--stats")
        .arg("--eager-qi")
        .arg(eager_qi.to_string())
        .output()
        .expect("Failed to execute solver");

    assert!(
        output.status.success(),
        "solver failed: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let result = String::from_utf8_lossy(&output.stdout).trim().to_string();
    let stats = serde_json::from_slice(&output.stderr).expect("Failed to parse solver statistics");
    (result, stats)
}

#[test]
fn eager_instantiation_before_model_regression() {
    let query =
        "tests/regression/smt_files/edge_cases_quantifiers/eager-instantiation-before-model.smt2";

    let (lazy_result, lazy_stats) = run_with_stats(query, 0);
    assert_eq!(lazy_result, "unsat");
    assert!(
        lazy_stats["arith_checks"].as_u64().unwrap() > 0,
        "an eager QI limit of zero must wait for a complete-model check"
    );

    let (eager_result, eager_stats) = run_with_stats(query, 1);
    assert_eq!(eager_result, "unsat");
    assert!(
        eager_stats["instantiations"].as_u64().unwrap() > 0,
        "the contradiction must use a quantifier instance"
    );
    assert_eq!(
        eager_stats["arith_checks"].as_u64(),
        Some(0),
        "eager QI should refute this query before a complete-model check"
    );
}

#[test]
fn eager_instantiation_drains_round_before_refresh_regression() {
    let query = "tests/regression/smt_files/edge_cases_quantifiers/eager-instantiation-queue.smt2";
    let (result, stats) = run_with_stats(query, 1);

    assert_eq!(result, "unsat");
    assert_eq!(
        stats["instantiations"].as_u64(),
        Some(3),
        "all three candidates from the first matching round must be materialized"
    );
    assert_eq!(
        stats["instantiation_rounds"].as_u64(),
        Some(1),
        "pending candidates must be drained without refreshing trigger matches"
    );
}

#[test]
fn eager_instantiation_full_round_regression() {
    let query = "tests/regression/smt_files/edge_cases_quantifiers/eager-instantiation-queue.smt2";
    let (result, stats) = run_with_stats(query, -1);

    assert_eq!(result, "unsat");
    assert_eq!(
        stats["instantiations"].as_u64(),
        Some(3),
        "-1 must exhaust every candidate in the matching round"
    );
    assert_eq!(
        stats["instantiation_rounds"].as_u64(),
        Some(1),
        "-1 must start only one matching round during the level visit"
    );
}

#[test]
fn regression_test() {
    let smt_files_dir = Path::new("tests/regression/smt_files");
    let expected_results_path = Path::new("tests/regression/expected_results.json");

    // Read expected results
    let expected_results: serde_json::Value = serde_json::from_str(
        &fs::read_to_string(expected_results_path).expect("Failed to read expected results"),
    )
    .expect("Failed to parse expected results");

    // Check if a specific subfolder is requested via environment variable
    let target_subfolder = env::var("TEST_SUBFOLDER").ok();

    // Get all subdirectories in smt_files
    let subdirs = fs::read_dir(smt_files_dir)
        .expect("Failed to read smt_files directory")
        .filter_map(|entry| {
            let entry = entry.ok()?;
            if entry.file_type().ok()?.is_dir() {
                let path = entry.path();
                // If a specific subfolder is requested, only include that one
                if let Some(ref target) = target_subfolder {
                    if path.file_name()?.to_str()? == target {
                        Some(path)
                    } else {
                        None
                    }
                } else {
                    Some(path)
                }
            } else {
                None
            }
        });

    // Statistics
    let mut correct = 0;
    let mut incorrect = 0;
    let mut timeout = 0;
    let mut total = 0;

    // Process each subdirectory
    for subdir in subdirs {
        // continue;
        println!("\nProcessing directory: {}", subdir.display());

        // Get all .smt2 files in the subdirectory
        let smt_files = fs::read_dir(&subdir)
            .expect("Failed to read subdirectory")
            .filter_map(|entry| {
                let entry = entry.ok()?;
                if entry.file_type().ok()?.is_file()
                    && entry.path().extension()?.to_str()? == "smt2"
                {
                    Some(entry.path())
                } else {
                    None
                }
            });

        // Process each SMT file
        for path in smt_files {
            total += 1;
            let relative_path = path
                .strip_prefix(smt_files_dir)
                .expect("Failed to get relative path")
                .to_str()
                .expect("Failed to convert path to string");

            // Get expected result
            let expected = if let Some(r) = expected_results[relative_path].as_str() {
                r
            } else {
                // omit tests with no expected results
                continue;
            };

            print!("Testing file: {} ... ", relative_path);
            io::stdout().flush().unwrap();

            // Optional arithmetic override (CI matrix passes SUNDANCE_ARITHMETIC to
            // exercise every backend against the same test corpus).
            let arithmetic = env::var("SUNDANCE_ARITHMETIC").ok();

            // Run solver with timeout
            let mut cmd = Command::new("target/release/sundance-smt");
            cmd.arg(path.to_str().unwrap());
            if let Some(ref a) = arithmetic {
                cmd.arg("--arithmetic").arg(a);
            }
            let child = cmd
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .expect("Failed to execute solver");

            // Wait for the process with timeout
            match wait_with_timeout(child, Duration::from_secs(10)) {
                Ok(output) => {
                    let actual = String::from_utf8_lossy(&output.stdout).trim().to_string();
                    if actual == expected {
                        correct += 1;
                        println!("\x1b[32m✓\x1b[0m");
                    } else {
                        incorrect += 1;
                        println!("\x1b[31m✗ (expected {}, got {})\x1b[0m", expected, actual);
                    }
                }
                Err(mut child) => {
                    timeout += 1;
                    println!("\x1b[33m⏱ (timeout)\x1b[0m");
                    // Kill the process if it's still running
                    let _ = child.kill();
                }
            };
        }
    }

    // Print summary
    println!("\nTest Summary:");
    println!("Total tests: {}", total);
    println!("Correct:     {}", correct);
    println!("Incorrect:   {}", incorrect);
    println!("Timeout:     {}", timeout);

    // Fail the test if there were any incorrect results
    if incorrect > 0 {
        panic!("{} tests failed", incorrect);
    }
}

/// Rejection tests (issue #52): every file under `tests/regression/rejection`
/// must make the solver error out rather than answer, so it must NOT print
/// `sat`, `unsat`, or `unknown` (`unknown` is a sound answer, not a rejection).
/// Forced onto the internal backend, since rejecting e.g. non-linear
/// multiplication is a property of the internal solver.
#[test]
fn rejection_test() {
    let rejection_dir = Path::new("tests/regression/rejection");

    let smt_files = fs::read_dir(rejection_dir)
        .expect("Failed to read rejection directory")
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            if entry.file_type().ok()?.is_file() && path.extension()?.to_str()? == "smt2" {
                Some(path)
            } else {
                None
            }
        });

    let mut rejected = 0;
    let mut answered = Vec::new();

    for path in smt_files {
        let name = path.file_name().unwrap().to_str().unwrap().to_string();
        print!("Rejection test: {} ... ", name);
        io::stdout().flush().unwrap();

        let mut cmd = Command::new("target/release/sundance-smt");
        cmd.arg(path.to_str().unwrap());
        // Force the internal backend: rejection of unsupported arithmetic (e.g.
        // non-linear multiplication) is a property of the internal solver.
        cmd.arg("--arithmetic").arg("internal");
        let child = cmd
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .expect("Failed to execute solver");

        match wait_with_timeout(child, Duration::from_secs(10)) {
            Ok(output) => {
                let actual = String::from_utf8_lossy(&output.stdout).trim().to_string();
                if actual == "sat" || actual == "unsat" || actual == "unknown" {
                    // The solver produced an answer for an input it should have
                    // rejected (errored on) instead.
                    answered.push(format!("{} (got {})", name, actual));
                    println!("\x1b[31m✗ (expected rejection, got {})\x1b[0m", actual);
                } else {
                    // Empty/other output means the solver errored out (e.g. the
                    // panic on non-linear multiplication) — a rejection.
                    rejected += 1;
                    println!("\x1b[32m✓ (rejected)\x1b[0m");
                }
            }
            Err(mut child) => {
                let _ = child.kill();
                answered.push(format!("{} (timeout)", name));
                println!("\x1b[31m✗ (expected rejection, timed out)\x1b[0m");
            }
        }
    }

    println!("\nRejection Test Summary:");
    println!("Rejected:            {}", rejected);
    println!("Answered (unexpected): {}", answered.len());

    if !answered.is_empty() {
        panic!(
            "{} input(s) were answered instead of rejected: {:?}",
            answered.len(),
            answered
        );
    }
}

fn wait_with_timeout(mut child: Child, timeout: Duration) -> Result<std::process::Output, Child> {
    let start = std::time::Instant::now();

    loop {
        match child.try_wait() {
            Ok(Some(_)) => {
                // Process has completed, get its output
                return Ok(child
                    .wait_with_output()
                    .expect("Failed to get process output"));
            }
            Ok(None) => {
                // Process is still running
                if start.elapsed() > timeout {
                    return Err(child);
                }
                thread::sleep(Duration::from_millis(100));
            }
            Err(e) => {
                panic!("Error waiting for process: {}", e);
            }
        }
    }
}
