// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Checks that the trimmed eDRAT proofs `--proof` writes for the files in
//! `tests/regression/smt_files/edrat_trimming` are well-formed: each Skolem constant is
//! declared before it is used, and each literal in a clause is defined before the clause.

use std::collections::HashSet;
use std::fs;
use std::path::Path;
use std::process::Command;

const SMT_FILES_DIR: &str = "tests/regression/smt_files/edrat_trimming";
const SKOLEM_PREFIX: &str = "skolem-variable-";

/// Returns the eDRAT proof Sundance writes for the unsat file `smt_file`.
fn trimmed_proof(smt_file: &Path) -> String {
    let stem = smt_file.file_stem().unwrap().to_str().unwrap();
    let proof_file = std::env::temp_dir().join(format!(
        "sundance-edrat-test-{}-{stem}.edrat",
        std::process::id()
    ));
    let output = Command::new(env!("CARGO_BIN_EXE_sundance-smt"))
        .arg(smt_file)
        .arg(format!("--proof={}", proof_file.display()))
        .output()
        .expect("Failed to execute solver");
    assert_eq!(
        String::from_utf8_lossy(&output.stdout).trim(),
        "unsat",
        "{}",
        smt_file.display()
    );
    let proof = fs::read_to_string(&proof_file).expect("Failed to read the proof");
    let _ = fs::remove_file(&proof_file);
    proof
}

/// The Skolem constants mentioned in `line`.
fn skolem_constants(line: &str) -> Vec<&str> {
    line.match_indices(SKOLEM_PREFIX)
        .map(|(start, _)| {
            let digits = line[start + SKOLEM_PREFIX.len()..]
                .find(|c: char| !c.is_ascii_digit())
                .unwrap_or(line.len() - start - SKOLEM_PREFIX.len());
            &line[start..start + SKOLEM_PREFIX.len() + digits]
        })
        .collect()
}

/// Panics with the offending line if `proof` is not well-formed.
fn check_well_formed(name: &str, proof: &str) {
    let mut literals: HashSet<i32> = HashSet::new();
    let mut skolems: HashSet<&str> = HashSet::new();
    for (i, line) in proof.lines().enumerate() {
        let context = || format!("{name}, proof line {}: {line}\n{proof}", i + 1);
        let tokens: Vec<&str> = line.split_whitespace().collect();
        if let Some(rest) = line.strip_prefix("(declare-skolem ") {
            skolems.insert(rest.split_whitespace().nth(2).unwrap());
        } else if let Some(rest) = line.strip_prefix("(edrat-literal ") {
            for skolem in skolem_constants(line) {
                assert!(
                    skolems.contains(skolem),
                    "undeclared {skolem} in {}",
                    context()
                );
            }
            literals.insert(rest.split_whitespace().next().unwrap().parse().unwrap());
        } else if !line.starts_with('(') && !line.starts_with(';') && !tokens.is_empty() {
            let clause = match tokens[0] {
                "d" => continue,
                "t" => &tokens[2..],
                "a" | "q" | "s" => &tokens[1..],
                _ => &tokens[..],
            };
            let (zero, clause) = clause.split_last().unwrap();
            assert_eq!(*zero, "0", "{}", context());
            for lit in clause {
                let lit: i32 = lit.parse().unwrap();
                assert!(
                    literals.contains(&lit.abs()),
                    "literal {lit} used before its definition in {}",
                    context()
                );
            }
        }
    }
}

#[test]
fn trimmed_edrat_proofs_are_well_formed() {
    let mut files: Vec<_> = fs::read_dir(SMT_FILES_DIR)
        .expect("Failed to read the eDRAT test directory")
        .map(|entry| entry.unwrap().path())
        .filter(|path| path.extension().is_some_and(|e| e == "smt2"))
        .collect();
    files.sort();
    assert!(!files.is_empty());
    for file in files {
        check_well_formed(&file.display().to_string(), &trimmed_proof(&file));
    }
}
