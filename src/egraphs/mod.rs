// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

pub mod basic;
pub mod traits;

// Public re-exports
pub use basic::egraph::{self, Egraph};
pub use basic::repr::{self, EgraphId, Op, Pattern, PatternId};
pub use traits::{EgraphTrait, Conflict, EgraphResult, Lit};

// Crate-internal re-exports (maintain old paths for internal code)
pub(crate) use basic::{datastructures, proofforest, unionfind, congruence_closure, utils};
