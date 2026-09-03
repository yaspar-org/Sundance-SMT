// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

pub mod basic;
pub mod traits;

// Public re-exports (stable interface)
pub use basic::egraph::Egraph;
pub use basic::repr::{self, EgraphId, Op, Pattern, PatternId};
pub use traits::{Conflict, EClassMemberRange, EgraphMergeEvent, EgraphResult, EgraphTrait, Lit};
