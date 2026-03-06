// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Micro-benchmarks for the arithmetic solver's tableau implementations.
//!
//! To run the benchmarks, use `cargo bench`.

use criterion::{Criterion, criterion_group, criterion_main};
use sundance_smt::arithmetic::lia::tableau::Tableau;
use sundance_smt::arithmetic::lia::tableau_dense::TableauDense;
use sundance_smt::arithmetic::lia::tableau_sparse::TableauSparse;
use sundance_smt::arithmetic::lia::types::Rational;

fn benchmark_pivot(c: &mut Criterion) {
    // Generate 20 tuples on the diagonal with values > 1
    let mut tuples: Vec<(usize, usize, Rational)> = (0..20)
        .map(|i| {
            let row = i;
            let col = i;
            let value = Rational::from(i as i64 + 2); // values >= 2
            (row, col, value)
        })
        .collect();
    // add 5 non-zero entries to the pivot row
    tuples.extend(
        (0..5)
            .map(|i| {
                let row = 0;
                let col = (i * 4 + 2) % 20;
                let value = Rational::from(10 * i as i64 + 2);
                (row, col, value)
            })
            .collect::<Vec<_>>(),
    );
    // add 5 non-zero entries to the pivot col
    tuples.extend(
        (0..5)
            .map(|i| {
                let row = (i * 4 + 3) % 20;
                let col = 0;
                let value = Rational::from(100 * i as i64 + 2);
                (row, col, value)
            })
            .collect::<Vec<_>>(),
    );
    // tuples now has 30 non-zero elements out of 400

    c.bench_function("dense_pivot_0_0_100x", |b| {
        b.iter(|| {
            let mut tableau = TableauDense::from_tuples(20, 20, tuples.clone()).unwrap();
            for _ in 0..100 {
                tableau.pivot(0, 0).expect("failed to dense pivot");
            }
        })
    });

    c.bench_function("sparse_pivot_0_0_100x", |b| {
        b.iter(|| {
            let mut tableau = TableauSparse::from_tuples(20, 20, tuples.clone()).unwrap();
            for _ in 0..100 {
                tableau.pivot(0, 0).expect("failed to dense pivot");
            }
        })
    });
}

criterion_group!(benches, benchmark_pivot);
criterion_main!(benches);
