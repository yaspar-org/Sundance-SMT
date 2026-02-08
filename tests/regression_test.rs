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

    writeln!(io::stdout(), "Building release version...").unwrap();
    let build_result = Command::new("cargo")
        .args(["build", "--release"])
        .output()
        .expect("Failed to execute cargo build");

    if !build_result.status.success() {
        panic!(
            "Failed to build release version for testing. Build stderr: {}",
            String::from_utf8_lossy(&build_result.stderr)
        );
    }
    writeln!(io::stdout(), "Release build completed successfully.").unwrap();

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
        writeln!(io::stdout(), "\nProcessing directory: {}", subdir.display()).unwrap();

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

            write!(io::stdout(), "Testing file: {} ... ", relative_path).unwrap();
            io::stdout().flush().unwrap();

            // Get expected result
            let expected = expected_results[relative_path]
                .as_str()
                .expect(&format!("No expected result found for {}", relative_path));

            // Run solver with timeout
            let child = Command::new("target/release/sundance_smt")
                .args([path.to_str().unwrap()])
                .stdout(std::process::Stdio::piped())
                .stderr(std::process::Stdio::piped())
                .spawn()
                .expect("Failed to execute solver");

            // Wait for the process with timeout
            let _ = match wait_with_timeout(child, Duration::from_secs(10)) {
                Ok(output) => {
                    let actual = String::from_utf8_lossy(&output.stdout).trim().to_string();
                    if actual == expected {
                        correct += 1;
                        writeln!(io::stdout(), "\x1b[32m✓\x1b[0m").unwrap();
                    } else {
                        incorrect += 1;
                        writeln!(
                            io::stdout(),
                            "\x1b[31m✗ (expected {}, got {})\x1b[0m",
                            expected,
                            actual
                        )
                        .unwrap();
                    }
                }
                Err(mut child) => {
                    timeout += 1;
                    writeln!(io::stdout(), "\x1b[33m⏱ (timeout)\x1b[0m").unwrap();
                    // Kill the process if it's still running
                    let _ = child.kill();
                }
            };
        }
    }

    // Print summary
    writeln!(io::stdout(), "\nTest Summary:").unwrap();
    writeln!(io::stdout(), "Total tests: {}", total).unwrap();
    writeln!(io::stdout(), "Correct:     {}", correct).unwrap();
    writeln!(io::stdout(), "Incorrect:   {}", incorrect).unwrap();
    writeln!(io::stdout(), "Timeout:     {}", timeout).unwrap();

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
