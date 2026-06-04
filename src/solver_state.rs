// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The `SolverState` struct owns the egraph and all solver-level state
//! (CNF cache, quantifiers, datatypes, theory combination, etc.).
//!
//! External code (propagator, main, quantifier instantiation, etc.) interacts
//! with `SolverState`; the egraph is an internal component accessible via
//! `solver_state.egraph`.

use std::collections::{HashMap, HashSet};

use yaspar_ir::ast::{Context, Term};

use crate::cnf::CNFCache;
use crate::datatypes::process::DatatypeInfo;
use crate::egraphs::datastructures::{
    Assertion, ConstructorType, Quantifier, TermOption,
};
use crate::egraphs::egraph::Egraph;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};

/// Solver-level state that wraps the egraph with theory-specific bookkeeping.
///
/// For now, the `Context` (term allocator) is accessed via `self.egraph.context`.
/// It will be moved here in a later step.
pub struct SolverState {
    /// The core egraph (union-find, congruence closure, predecessors, backtracking).
    pub egraph: Egraph,

    /// Maps u64 term UIDs to Term objects.
    pub terms_list: Vec<TermOption>,

    /// Cached assertions (equality, disequality, distinct, tester).
    pub assertions: Vec<Assertion>,

    /// Quantifier instances with triggers and guards.
    pub quantifiers: Vec<Quantifier>,

    /// Tracks quantifier instantiations to avoid duplicates.
    pub added_instantiations: HashMap<u64, HashSet<DeterministicHashMap<String, Term>>>,

    /// Tracks skolemized quantifiers.
    pub added_skolemizations: DeterministicHashSet<u64>,

    /// Terms created by quantifier instantiation and their predecessors.
    pub predecessors_created_by_quantifiers: DeterministicHashMap<u64, DeterministicHashSet<u64>>,

    /// Precomputed datatype constructor/selector info.
    pub datatype_info: DatatypeInfo,

    /// Maps terms to their constructor type (for datatype theory).
    pub term_constructors: DeterministicHashMap<u64, ConstructorType>,

    /// Tracks (term, func, subterms) triples for e-class union after quantifier instantiation.
    pub union_to_eclass: DeterministicHashSet<(u64, String, Vec<u64>)>,

    /// Pairs of terms for which we have learnt x = y \/ x > y \/ x < y.
    pub nelson_oppen_ineq_literals: HashSet<(u64, u64)>,

    /// Terms for which datatype axioms have been applied.
    pub datatype_axioms_applied: HashSet<u64>,

    /// Arithmetic terms for Nelson-Oppen theory combination.
    pub arithmetic_terms: Vec<u64>,

    /// Bidirectional mapping: term UID <-> SAT literal.
    pub cnf_cache: CNFCache,

    /// Whether to instantiate some datatype axioms lazily.
    pub lazy_dt: bool,

    /// Whether DDSMT optimizations are on (experimental, buggy).
    pub ddsmt: bool,

    /// Whether to skolemize eagerly.
    pub eager_skolem: bool,
}

impl SolverState {
    /// Create a new SolverState. Takes ownership of the Context and config flags,
    /// creates the inner Egraph using the existing constructor.
    pub fn new(context: Context, lazy_dt: bool, ddsmt: bool, eager_skolem: bool) -> Self {
        let datatype_info = DatatypeInfo::from_context(&context);
        let egraph = Egraph::new(context, lazy_dt, ddsmt, eager_skolem);

        SolverState {
            terms_list: vec![TermOption::None],
            assertions: vec![],
            quantifiers: vec![],
            added_instantiations: HashMap::default(),
            added_skolemizations: DeterministicHashSet::default(),
            predecessors_created_by_quantifiers: DeterministicHashMap::new(),
            datatype_info,
            term_constructors: DeterministicHashMap::new(),
            union_to_eclass: DeterministicHashSet::new(),
            nelson_oppen_ineq_literals: HashSet::new(),
            datatype_axioms_applied: HashSet::new(),
            arithmetic_terms: vec![],
            cnf_cache: Default::default(),
            lazy_dt,
            ddsmt,
            eager_skolem,
            egraph,
        }
    }
}
