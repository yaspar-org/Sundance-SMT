// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use std::env;
use std::fs;
use std::io::{self, Write};
use std::path::Path;
use std::process::{Child, Command};
use std::thread;
use std::time::Duration;

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

            print!("Testing file: {} ... ", relative_path);
            io::stdout().flush().unwrap();

            // Get expected result
            let expected = expected_results[relative_path]
                .as_str()
                .unwrap_or_else(|| panic!("No expected result found for {}", relative_path));

            // Run solver with timeout
            let child = Command::new("target/release/sundance-smt")
                .args([path.to_str().unwrap()])
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
