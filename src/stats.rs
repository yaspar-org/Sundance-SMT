// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Global statistics counters for Sundance, accessible from signal handlers.

use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// Whether stats collection is enabled.
pub static STATS_ENABLED: AtomicBool = AtomicBool::new(false);

/// Number of quantifiers in the input problem.
pub static NUM_QUANTIFIERS: AtomicUsize = AtomicUsize::new(0);

/// Total number of quantifier instantiations performed so far.
pub static NUM_INSTANTIATIONS: AtomicUsize = AtomicUsize::new(0);

/// Increment the instantiation counter by `n`.
#[inline]
pub fn add_instantiations(n: usize) {
    NUM_INSTANTIATIONS.fetch_add(n, Ordering::Relaxed);
}

/// Print current stats to stderr. Safe to call from a signal handler
/// (uses write! to stderr which is typically unbuffered).
pub fn print_stats_to_stderr() {
    let nq = NUM_QUANTIFIERS.load(Ordering::Relaxed);
    let ni = NUM_INSTANTIATIONS.load(Ordering::Relaxed);
    eprintln!("num-quantifiers: {nq}");
    eprintln!("num-instantiations: {ni}");
}
