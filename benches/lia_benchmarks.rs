// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use criterion::{Criterion, criterion_group, criterion_main};
use sundance_smt::arithmetic::lia::config::SolverConfig;
use sundance_smt::arithmetic::lia::frontend::solve_smtlib;

// SAT benchmark
const LIA_00000: &str = include_str!("data/lia_00000_a1a014bc.smt2");
// SAT benchmark
const LIA_00508: &str = include_str!("data/lia_00508_532fc04c.smt2");
// UNSAT benchmark
const LIA_00301_1: &str = include_str!("data/lia_00301_06f02f64_unsat.smt2");
// UNSAT benchmark
const LIA_00301_2: &str = include_str!("data/lia_00301_6af0beef_unsat.smt2");

fn benchmark_lia_00000(c: &mut Criterion) {
    let config = SolverConfig::default();
    c.bench_function("lia_00000_a1a014bc", |b| {
        b.iter(|| {
            solve_smtlib(LIA_00000, &config).expect("solver failed");
        })
    });
}

fn benchmark_lia_00508(c: &mut Criterion) {
    let config = SolverConfig::default();
    c.bench_function("lia_00508_532fc04c", |b| {
        b.iter(|| {
            solve_smtlib(LIA_00508, &config).expect("solver failed");
        })
    });
}

fn benchmark_lia_00301_1(c: &mut Criterion) {
    let config = SolverConfig::default();
    c.bench_function("lia_00301_06f02f64_unsat", |b| {
        b.iter(|| {
            solve_smtlib(LIA_00301_1, &config).expect("solver failed");
        })
    });
}

fn benchmark_lia_00301_2(c: &mut Criterion) {
    let config = SolverConfig::default();
    c.bench_function("lia_00301_6af0beef_unsat.smt2", |b| {
        b.iter(|| {
            solve_smtlib(LIA_00301_2, &config).expect("solver failed");
        })
    });
}

criterion_group!(
    benches,
    benchmark_lia_00000,
    benchmark_lia_00508,
    benchmark_lia_00301_1,
    benchmark_lia_00301_2
);
criterion_main!(benches);
