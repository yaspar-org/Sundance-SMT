// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

pub mod basic;
#[cfg(feature = "semper-egraph")]
pub mod semper;
pub mod traits;

/// Trail-boundary profile, symmetric across backends: wall spent inside the
/// EgraphTrait `notify_new_decision_level` and `backtrack_to` implementations,
/// so for semper it includes the adapter-side replay/rebuild that the engine's
/// SEMPER_PROF restore figure excludes. Enabled by TRAIL_PROF; each backend
/// prints the totals when the solve tears the e-graph down.
pub mod trail_prof {
    use std::sync::OnceLock;
    use std::sync::atomic::{AtomicU64, Ordering};

    static LEVEL_NS: AtomicU64 = AtomicU64::new(0);
    static LEVEL_CALLS: AtomicU64 = AtomicU64::new(0);
    static BT_NS: AtomicU64 = AtomicU64::new(0);
    static BT_CALLS: AtomicU64 = AtomicU64::new(0);

    pub fn enabled() -> bool {
        static ON: OnceLock<bool> = OnceLock::new();
        *ON.get_or_init(|| std::env::var_os("TRAIL_PROF").is_some())
    }

    pub fn record_level(ns: u64) {
        LEVEL_NS.fetch_add(ns, Ordering::Relaxed);
        LEVEL_CALLS.fetch_add(1, Ordering::Relaxed);
    }

    pub fn record_backtrack(ns: u64) {
        BT_NS.fetch_add(ns, Ordering::Relaxed);
        BT_CALLS.fetch_add(1, Ordering::Relaxed);
    }

    pub fn report(backend: &str) {
        if enabled() {
            eprintln!(
                "TRAIL_PROF backend={backend} level_ns={} level_calls={} \
                 backtrack_ns={} backtrack_calls={}",
                LEVEL_NS.swap(0, Ordering::Relaxed),
                LEVEL_CALLS.swap(0, Ordering::Relaxed),
                BT_NS.swap(0, Ordering::Relaxed),
                BT_CALLS.swap(0, Ordering::Relaxed),
            );
        }
    }
}

// Public re-exports (stable interface)
pub use basic::egraph::Egraph;
pub use basic::repr::{self, EgraphId, Op, Pattern, PatternId};
pub use traits::{Conflict, EgraphResult, EgraphTrait, Lit};
