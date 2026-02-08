# Regression Tests

This directory contains regression tests for the ArgAtsSundanceEgraphs SMT solver.

## Directory Structure

- `smt_files/`: Contains SMT2 files to test
- `expected_results.json`: Maps SMT file names to their expected results (sat/unsat)

## Adding New Tests

1. Add your SMT2 file to the `smt_files/` directory
2. Add an entry to `expected_results.json` with the expected result
3. Run the tests using `cargo test regression`

## Test Format

Each SMT2 file should be a valid SMT-LIB 2.6 script. The expected result should be either "sat" or "unsat". 