// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! The `SolverState` struct owns the egraph and all solver-level state
//! (CNF cache, quantifiers, datatypes, theory combination, etc.).
//!
//! External code (propagator, main, quantifier instantiation, etc.) interacts
//! with `SolverState`; the egraph is an internal component accessible via
//! `solver_state.egraph`.

use std::collections::{HashMap, HashSet};
use sat_interface::Formula;
use yaspar_ir::ast::alg::CheckIdentifier;
use yaspar_ir::ast::{Arena, Attribute, Context, FetchSort, HasArena, IdentifierKind, Monomorphization, Repr, Str, Term, TermAllocator};
use yaspar_ir::ast::ATerm::*;

use crate::cnf::{CNFCache, CNFConversion, CNFEnv};
use crate::datatypes::axioms::{learn_ctor_selector_clauses, learn_or_not_term_tester_term};
use crate::datatypes::process::DatatypeInfo;
use crate::debug_println;
use crate::solver_types::{
    Assertion, ConstructorType, ConstructorType::*, Polarity, Quantifier, TermOption,
};
use crate::egraphs::basic::egraph::Egraph;
use crate::egraphs::traits::EgraphTrait;

use crate::log::is_important;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};

fn get_subterms(term: &Term) -> (String, Vec<&Term>) {
    match term.repr() {
        Annotated(term, _) => {
            let (func, mut subterms) = get_subterms(term);
            subterms.push(term);
            (func, subterms)
        }
        Eq(left, right) => ("=".to_string(), vec![left, right]),
        Distinct(items) => ("distinct".to_string(), items.iter().collect()),
        And(items) => ("and".to_string(), items.iter().collect()),
        Or(items) => ("or".to_string(), items.iter().collect()),
        Xor(items) => ("xor".to_string(), items.iter().collect()),
        App(func, items, _) => {
            let func_indices = &func.0.indices;
            let func_id = func.id_str();
            if func_indices.is_empty() {
                (func_id.get().clone(), items.iter().collect())
            } else {
                let r = format!("(is {})", func_indices[0].clone());
                (r, items.iter().collect())
            }
        }
        Implies(left, right) => {
            let mut subterms: Vec<&Term> = left.iter().collect();
            subterms.push(right);
            ("=>".to_string(), subterms)
        }
        Not(t) => ("not".to_string(), vec![t]),
        Ite(b, t1, t2) => ("ite".to_string(), vec![b, t1, t2]),
        Let(_, _) => panic!("We should have inlined all Let bindings"),
        Matching(..) => todo!(),
        Forall(_, middle_term) | Exists(_, middle_term) => {
            if let Annotated(inner_term, attrs) = middle_term.repr() {
                let mut subterms = vec![inner_term];
                for attr in attrs.iter() {
                    if let Attribute::Pattern(s_exprs) = &attr {
                        subterms.extend(s_exprs.iter());
                    }
                }
                let name = if let Forall(..) = term.repr() {
                    "forall".to_string()
                } else {
                    "exists".to_string()
                };
                (name, subterms)
            } else {
                panic!("We have a forall/exists case that is not annotated");
            }
        }
        Constant(..) | Global(..) | Local(..) => ("".to_string(), vec![]),
    }
}

/// Solver-level state that wraps the egraph with theory-specific bookkeeping.
///
/// For now, the `Context` (term allocator) is accessed via `self.egraph.context`.
/// It will be moved here in a later step.
pub struct SolverState {
    pub context: Context,
    /// The core egraph (union-find, congruence closure, predecessors, backtracking).
    pub egraph: Egraph,

    /// Solver UIDs for true and false constants
    pub true_uid: u64,
    pub false_uid: u64,

    /// Solver-level hash for tracking validity of recorded facts across backtracking.
    pub current_hash: u32,
    /// Maps decision level -> hash at which that level was entered.
    pub hash_at_level: Vec<u32>,

    /// Bidirectional mapping between solver term UIDs and egraph term IDs
    pub id_map: bimap::BiMap<u64, u32>,

    /// Map from term UID to yaspar Term objects (solver-level, not in egraph)
    pub terms_list: Vec<TermOption>,

    /// Cached assertions (equality, disequality, distinct, tester).
    pub assertions: Vec<Assertion>,

    /// Quantifier instances with triggers and guards.
    pub quantifiers: Vec<Quantifier>,

    /// Tracks quantifier instantiations to avoid duplicates.
    pub added_instantiations: HashMap<u64, HashSet<DeterministicHashMap<String, Term>>>,

    /// Tracks skolemized quantifiers.
    pub added_skolemizations: DeterministicHashSet<u64>,

    /// Precomputed datatype constructor/selector info.
    pub datatype_info: DatatypeInfo,

    /// Maps terms to their constructor type (for datatype theory).
    pub term_constructors: DeterministicHashMap<u64, ConstructorType>,

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
        let egraph = Egraph::new();
        let datatype_info = DatatypeInfo::from_context(&context);


        SolverState {
            context,
            true_uid: 0,
            false_uid: 0,
            current_hash: 1,
            hash_at_level: vec![1, 1],
            id_map: bimap::BiMap::new(),
            terms_list: vec![TermOption::None],
            assertions: vec![],
            quantifiers: vec![],
            added_instantiations: HashMap::default(),
            added_skolemizations: DeterministicHashSet::default(),
            datatype_info,
            term_constructors: DeterministicHashMap::new(),
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

    fn cnf_env(&mut self) -> CNFEnv<'_> {
        CNFEnv {
            context: &mut self.context,
            cache: &mut self.cnf_cache,
        }
    }

    pub fn is_valid_hash(&self, hash: u32, level: usize) -> bool {
        hash >= self.hash_at_level[level] || hash == 0 || level == 0
    }

    pub fn get_u64_from_lit_with_polarity(&self, lit: i32) -> (u64, bool) {
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            (*num, true)
        } else if let Some(num) = self.cnf_cache.var_map_reverse.get(&-lit) {
            (*num, false)
        } else {
            panic!("Term {} not found in cnf_cache", lit);
        }
    }

    pub fn get_lit_from_u64(&self, num: u64) -> i32 {
        *self.cnf_cache.var_map.get(&num).unwrap()
    }

    pub fn get_lit_from_u64_safe(&self, num: u64) -> Option<i32> {
        self.cnf_cache.var_map.get(&num).cloned()
    }

    pub fn get_term_from_lit(&mut self, lit: i32) -> Term {
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            self.get_term(*num)
        } else {
            let num = self.cnf_cache.var_map_reverse.get(&-lit).unwrap();
            self.context.not(self.get_term(*num))
        }
    }

    pub fn get_term_from_lit_safe(&mut self, lit: i32) -> Option<Term> {
        if let Some(num) = self.cnf_cache.var_map_reverse.get(&lit) {
            Some(self.get_term(*num))
        } else if let Some(num) = self.cnf_cache.var_map_reverse.get(&-lit) {
            Some(self.context.not(self.get_term(*num)))
        } else {
            None
        }
    }

    pub fn get_lit_from_term(&self, term: &Term) -> i32 {
        let num = term.uid();
        *self.cnf_cache.var_map.get(&num).unwrap()
    }

    /// Convert an equality between two egraph IDs to a SAT literal.
    pub fn make_eq(&mut self, x: u32, y: u32) -> i32 {
        let true_id = self.to_egraph_id(self.true_uid);
        let false_id = self.to_egraph_id(self.false_uid);
        if (x == false_id && y == true_id) || (x == true_id && y == false_id) {
            self.get_lit_from_u64(self.to_solver_uid(false_id))
        } else if (x == true_id && y == true_id) || (x == false_id && y == false_id) {
            self.get_lit_from_u64(self.to_solver_uid(true_id))
        } else if x == true_id {
            self.get_lit_from_u64(self.to_solver_uid(y))
        } else if y == true_id {
            self.get_lit_from_u64(self.to_solver_uid(x))
        } else if x == false_id {
            -self.get_lit_from_u64(self.to_solver_uid(y))
        } else if y == false_id {
            -self.get_lit_from_u64(self.to_solver_uid(x))
        } else {
            let sx = self.to_solver_uid(x);
            let sy = self.to_solver_uid(y);
            let eq_term_class = self.context.eq(self.get_term(sx), self.get_term(sy));
            self.get_lit_from_term(&eq_term_class)
        }
    }

    pub fn get_term(&self, num: u64) -> Term {
        self.terms_list[num as usize].clone().unwrap()
    }

    pub fn get_term_ref(&self, num: u64) -> &Term {
        match &self.terms_list[num as usize] {
            TermOption::Some(term) | TermOption::Uninitialized(term) => term,
            TermOption::None => panic!("get_term_ref: no term for id {}", num),
        }
    }

    pub fn get_term_safe(&self, num: u64) -> TermOption {
        if self.terms_list.len() <= num as usize {
            TermOption::None
        } else {
            self.terms_list[num as usize].clone()
        }
    }

    /// Convert a solver term UID to the corresponding egraph ID.
    pub fn to_egraph_id(&self, solver_uid: u64) -> u32 {
        *self.id_map.get_by_left(&solver_uid)
            .unwrap_or_else(|| panic!("to_egraph_id: no egraph ID for solver uid {}", solver_uid))
    }

    /// Convert an egraph term ID to the corresponding solver UID.
    pub fn to_solver_uid(&self, egraph_id: u32) -> u64 {
        *self.id_map.get_by_right(&egraph_id)
            .unwrap_or_else(|| panic!("to_solver_uid: no solver uid for egraph id {}", egraph_id))
    }

    pub fn check_for_recursive_datatypes(&self) -> Option<Str> {
        self.datatype_info
            .contains_recursive_datatype(&self.context)
    }

    /// Register true and false in both the egraph and the solver's ID mapping.
    pub fn register_bool_constants(&mut self, true_term: &Term, false_term: &Term) {
        use crate::egraphs::traits::EgraphTrait;
        let true_egraph_id = self.egraph.register_true();
        let false_egraph_id = self.egraph.register_false();

        let true_uid = true_term.uid();
        let false_uid = false_term.uid();
        self.true_uid = true_uid;
        self.false_uid = false_uid;
        let max_uid = std::cmp::max(true_uid, false_uid) as usize;
        while self.terms_list.len() <= max_uid {
            self.terms_list.resize(self.terms_list.len() * 2, TermOption::None);
        }
        self.terms_list[true_uid as usize] = TermOption::Some(true_term.clone());
        self.terms_list[false_uid as usize] = TermOption::Some(false_term.clone());
        self.id_map.insert(true_uid, true_egraph_id);
        self.id_map.insert(false_uid, false_egraph_id);
    }

    /// Extract Op from a yaspar Term.
    fn extract_op(term: &Term) -> crate::egraphs::repr::Op {
        use crate::egraphs::repr::Op;
        match term.repr() {
            Eq(_, _) => Op::Eq,
            Ite(_, _, _) => Op::Ite,
            Not(_) => Op::Not,
            And(_) => Op::And,
            Or(_) => Op::Or,
            Implies(_, _) => Op::Implies,
            Distinct(_) => Op::Distinct,
            App(f, _, _) => {
                let func_indices = &f.0.indices;
                if func_indices.is_empty() {
                    Op::App(f.id_str().get().to_string())
                } else {
                    // Indexed function (like (_ is Ctor)) — include indices in key
                    let key = format!("({} {})", f.id_str().get(), func_indices[0]);
                    Op::App(key)
                }
            }
            Global(qid, _) => Op::Constant(qid.id_str().get().to_string()),
            Constant(c, _) => Op::Constant(format!("{:?}", c)),
            Local(local) => Op::Local(local.symbol.to_string()),
            _ => panic!("extract_op: unsupported term type {:?}", term.repr()),
        }
    }

    /// Solver-level recursive term registration (bottom-up).
    /// Recurses into subterms first, then registers this term.
    /// This guarantees children exist before parents in the egraph.
    pub fn insert_predecessor(
        &mut self,
        term: &Term,
        _parent: Option<u64>,
        guard: Option<u64>,
        from_quantifier: bool,
    ) -> u32 {

        let num = term.uid();

        // Early return if already registered
        while self.terms_list.len() <= num as usize {
            self.terms_list.resize(self.terms_list.len() * 2, TermOption::None);
            
        }
        if let TermOption::Some(_) = &self.terms_list[num as usize] {
            return self.to_egraph_id(num);
        }
        // Reuse egraph ID if build_pattern already allocated one for this term
        if let Some(eid) = self.id_map.get_by_left(&num).copied() {
            self.terms_list[num as usize] = TermOption::Some(term.clone());
            self.solver_walk_term(term, guard);
            return eid;
        }

        // Add term to solver's terms_list
        self.terms_list[num as usize] = TermOption::Some(term.clone());

        // For quantifier terms, register as opaque (no congruence)
        if let Exists(_, _) | Forall(_, _) = term.repr() {
            let egraph_id = self.egraph.register_opaque();
            self.id_map.insert(num, egraph_id);
            self.solver_walk_term(term, guard);
            return egraph_id;
        }

        // Recurse into subterms first (bottom-up: children before parents)
        let (_, subterms) = get_subterms(term);
        let egraph_children: Vec<u32> = subterms.iter()
            .map(|subterm| self.insert_predecessor(subterm, None, None, from_quantifier))
            .collect();

        // Register this term in the egraph
        let op = Self::extract_op(term);
        let egraph_id = self.egraph.register_term(op, &egraph_children, from_quantifier);
        self.id_map.insert(num, egraph_id);
        self.solver_walk_term(term, guard);
        egraph_id
    }

    /// Build a Pattern tree from a yaspar Term and compile it into the egraph.
    /// Returns the PatternId of the compiled pattern.
    fn build_pattern(&mut self, term: &Term) -> crate::egraphs::repr::PatternId {
        use crate::egraphs::EgraphTrait;
        let pattern = self.build_pattern_tree(term);
        self.egraph.compile_pattern(pattern)
    }

    /// Recursively build a Pattern tree from a yaspar Term (without compiling).
    fn build_pattern_tree(&mut self, term: &Term) -> crate::egraphs::repr::Pattern {
        use crate::egraphs::repr::{Pattern, Op};
        use crate::egraphs::EgraphTrait;

        let op = Self::extract_op(term);
        match &op {
            Op::Local(name) => Pattern::Var(name.clone()),
            Op::Constant(_) | Op::App(_) | Op::Eq | Op::Ite | Op::Not
            | Op::And | Op::Or | Op::Implies | Op::Distinct => {
                let (_, subterms) = get_subterms(term);
                if subterms.is_empty() {
                    let uid = term.uid();
                    let egraph_id = if let Some(&eid) = self.id_map.get_by_left(&uid) {
                        eid
                    } else {
                        let eid = self.egraph.register_term(op.clone(), &[], false);
                        self.id_map.insert(uid, eid);
                        while self.terms_list.len() <= uid as usize {
                            self.terms_list.resize(self.terms_list.len() * 2, TermOption::None);
                        }
                        if self.terms_list[uid as usize].is_none() {
                            self.terms_list[uid as usize] = TermOption::Uninitialized(term.clone());
                        }
                        eid
                    };
                    Pattern::Ground(egraph_id)
                } else {
                    let sub_patterns: Vec<Pattern> = subterms.iter()
                        .map(|s| self.build_pattern_tree(s))
                        .collect();
                    Pattern::App(op, sub_patterns)
                }
            }
        }
    }

    /// Walk the term tree for solver-level bookkeeping only.
    /// Tracks arithmetic terms and registers quantifiers.
    fn solver_walk_term(&mut self, term: &Term, guard: Option<u64>) {


        let num = term.uid();

        // Arithmetic term tracking
        if term.get_sort(self.context.arena()).to_string() == "Int" {
            if !self.arithmetic_terms.contains(&num) {
                self.arithmetic_terms.push(num);
            }
        }

        // Quantifier registration
        if let Exists(sorted_vars, middle_term) | Forall(sorted_vars, middle_term) = term.repr() {
            if let Annotated(inner_term, attrs) = middle_term.repr() {
                // Store quantifier body in terms_list (needed for substitution during instantiation)
                let body_uid = inner_term.uid();
                while self.terms_list.len() <= body_uid as usize {
                    self.terms_list.resize(self.terms_list.len() * 2, TermOption::None);
                }
                if self.terms_list[body_uid as usize].is_none() {
                    self.terms_list[body_uid as usize] = TermOption::Uninitialized(inner_term.clone());
                }

                let mut trigger_ids = vec![];

                for attr in attrs.iter() {
                    if let Attribute::Pattern(s_exprs) = attr {
                        let pattern_ids: Vec<crate::egraphs::repr::PatternId> = s_exprs.iter()
                            .map(|p| self.build_pattern(p))
                            .collect();
                        trigger_ids.push(pattern_ids);
                    }
                }

                let variables: Vec<String> = sorted_vars.iter().map(|x| x.0.to_string()).collect();

                let polarity = if let Forall(..) = term.repr() {
                    Polarity::Universal
                } else {
                    Polarity::Existential
                };

                self.quantifiers.push(Quantifier {
                    triggers: trigger_ids,
                    variables,
                    body: inner_term.uid(),
                    id: term.uid(),
                    guard,
                    polarity,
                    skolemized: false,
                });
            }
            // Don't recurse into quantifier bodies for solver bookkeeping
            return;
        }

        // Recurse into subterms
        let (_, subterms) = get_subterms(term);
        for subterm in &subterms {
            self.solver_walk_term(subterm, None);
        }
    }
}

impl HasArena for SolverState {
    fn arena(&mut self) -> &mut Arena {
        self.context.arena()
    }
}

impl<T> CNFConversion<SolverState> for T
where
    T: for<'a> CNFConversion<CNFEnv<'a>>,
{
    fn cnf_tseitin(&self, env: &mut SolverState) -> Formula {
        self.cnf_tseitin(&mut env.cnf_env())
    }

    fn nnf(&self, env: &mut SolverState) -> Self {
        self.nnf(&mut env.cnf_env())
    }
}

// impl Deref for SolverState {
//     type Target = Egraph;

//     fn deref(&self) -> &Egraph {
//         &self.egraph
//     }
// }

// impl DerefMut for SolverState {
//     fn deref_mut(&mut self) -> &mut Egraph {
//         &mut self.egraph
//     }
// }

/// Process a SAT literal assignment through the egraph.
/// This is the solver-level entry point that classifies the literal and
/// dispatches to the appropriate egraph operation (union, disequality, etc.).
pub fn process_assignment(
    lit: i32,
    solver_state: &mut SolverState,
    level: usize,
    fixed: bool,
) -> Option<Vec<Vec<i32>>> {
    use crate::egraphs::EgraphTrait;
    let lazy_dt = solver_state.lazy_dt;
    let ddsmt = solver_state.ddsmt;
    debug_println!(2, 0, "Processing literal {:} at level {}", lit, level);
    let sign = lit > 0;

    let term = solver_state.get_term_from_lit(lit.abs());
    debug_println!(24, 1, "Term: {}", term);
    let assertion = find_if_eq_diseq(&term, sign, solver_state, level, fixed);

    let true_egraph_id = solver_state.to_egraph_id(solver_state.true_uid);
    let false_egraph_id = solver_state.to_egraph_id(solver_state.false_uid);

    if let Some(t) = solver_state.cnf_cache.var_map_reverse.get(&lit) {
        let egraph_t = solver_state.to_egraph_id(*t);
        debug_println!(
            16,
            0,
            "We are in process_assignment, unioning with true for lit {} and t {} and true_term {}",
            lit,
            t,
            true_egraph_id
        );
        let union_result = solver_state.egraph.assert_equal(egraph_t, true_egraph_id, level);
        if let Some(conflict) = union_result.conflict {
            let mut model_terms: Vec<i32> = conflict.equalities
                .iter()
                .map(|(a, b)| -solver_state.make_eq(*a, *b))
                .collect();
            model_terms.push(-conflict.diseq_lit);
            return Some(vec![model_terms]);
        }
    }

    if let Some(t) = solver_state.cnf_cache.var_map_reverse.get(&-lit) {
        let egraph_t = solver_state.to_egraph_id(*t);
        debug_println!(
            16,
            0,
            "We are in process_assignment, unioning with false for lit {} and t {} and false_term {}",
            lit,
            t,
            false_egraph_id
        );
        let union_result = solver_state.egraph.assert_equal(egraph_t, false_egraph_id, level);
        if let Some(conflict) = union_result.conflict {
            let mut model_terms: Vec<i32> = conflict.equalities
                .iter()
                .map(|(a, b)| -solver_state.make_eq(*a, *b))
                .collect();
            model_terms.push(-conflict.diseq_lit);
            return Some(vec![model_terms]);
        };
    }

    debug_println!("Finished union to True/False");
    let additional_constraints = match assertion {
        Assertion::Tester {
            ctor_name,
            inner_term,
            term,
        } => {
            let dt_sort = inner_term.get_sort(solver_state);
            let _term_lit = solver_state.get_lit_from_term(&term);
            debug_println!(19, 0, "trying to get for the term {}", inner_term);
            match solver_state.term_constructors.get(&inner_term.uid()).unwrap() {
                Constructor {
                    name,
                    tester_term,
                    hash,
                    level,
                } if solver_state.is_valid_hash(*hash, *level) => {
                    debug_println!(
                        11,
                        2,
                        "We have a valid prior constructor with name {} (our tester name is {})",
                        name,
                        ctor_name
                    );
                    if *name == ctor_name {
                        debug_println!(11, 2, "name == ctor_name");
                        None
                    } else {
                        debug_println!(11, 2, "name != ctor_name");
                        let tester_cnf = learn_or_not_term_tester_term(
                            solver_state,
                            tester_term.clone(),
                            term.clone(),
                            true,
                        );
                        Some(tester_cnf)
                    }
                }
                _ => {
                    solver_state.term_constructors.insert(
                        inner_term.uid(),
                        Constructor {
                            name: ctor_name.clone(),
                            tester_term: term.clone(),
                            level,
                            hash: solver_state.current_hash,
                        },
                    );

                    if lazy_dt {
                        let dt_name = solver_state.datatype_info.constructors.get(&ctor_name).unwrap();
                        let dt_dec = solver_state.datatype_info.datatypes.get(dt_name).unwrap();
                        let dt_dec = dt_dec
                            .monomorphize(&dt_sort, solver_state.context.arena())
                            .expect("type invariant violation: datatype fails to monomorphize");

                        let ctor = dt_dec
                            .constructors
                            .iter()
                            .find(|ctor| ctor.ctor == ctor_name)
                            .expect("type checking invariance violation: datatypes")
                            .clone();

                        let ctor_selector_clauses: Vec<Vec<i32>> =
                            learn_ctor_selector_clauses(solver_state, &inner_term, &ctor, &dt_sort, true, ddsmt, lazy_dt);
                        Some(ctor_selector_clauses)
                    } else {
                        None
                    }
                }
            }
        }
        Assertion::Equality { t1, t2, level, .. } => {
            debug_println!(
                16,
                0,
                "Merging: {} = {}",
                solver_state.get_term(t1),
                solver_state.get_term(t2)
            );

            let et1 = solver_state.to_egraph_id(t1);
            let et2 = solver_state.to_egraph_id(t2);
            let union_result = solver_state.egraph.assert_equal(et1, et2, level);
            if let Some(conflict) = union_result.conflict {
                let mut model_terms: Vec<i32> = conflict.equalities
                    .iter()
                    .map(|(a, b)| -solver_state.make_eq(*a, *b))
                    .collect();
                model_terms.push(-conflict.diseq_lit);
                Some(vec![model_terms])
            } else {
                None
            }
        }
        Assertion::Disequality {
            t1,
            t2,
            level,
            ..
        } => {
            debug_println!(
                16,
                0,
                "Adding disequality {} ≠ {} to stack at level {:?}",
                solver_state.get_term(t1),
                solver_state.get_term(t2),
                level,
            );

            let et1 = solver_state.to_egraph_id(t1);
            let et2 = solver_state.to_egraph_id(t2);
            let result = solver_state.egraph.assert_disequal(et1, et2, lit, level);
            if let Some(conflict) = result.conflict {
                let mut model_terms: Vec<i32> = conflict.equalities
                    .into_iter()
                    .map(|(a, b)| -solver_state.make_eq(a, b))
                    .collect();
                model_terms.push(solver_state.make_eq(et1, et2));
                debug_println!(
                    16,
                    1,
                    "Contradiction found [1]: {:?} [{:?}]",
                    model_terms
                        .iter()
                        .map(|x| solver_state.get_term_from_lit(*x))
                        .collect::<Vec<_>>(),
                    model_terms
                );
                return Some(vec![model_terms]);
            }
            None
        }
        Assertion::Distinct { terms, level, .. } => {
            let egraph_terms: Vec<u32> = terms.iter()
                .map(|t| solver_state.to_egraph_id(*t))
                .collect();
            let result = solver_state.egraph.assert_distinct(&egraph_terms, lit, level);
            if let Some(conflict) = result.conflict {
                let mut model_terms: Vec<i32> = conflict.equalities
                    .into_iter()
                    .map(|(a, b)| -solver_state.make_eq(a, b))
                    .collect();
                model_terms.push(-conflict.diseq_lit);
                debug_println!(16, 0, "Contradiction found in distinct: {:?}", model_terms);
                return Some(vec![model_terms]);
            }
            None
        }
        Assertion::Other => None,
    };

    debug_println!(
        4,
        0,
        "We are in process_assignment, checking for contradiction with true and false",
    );
    if let Some(negated_model) =
        solver_state.egraph.explain_equality(true_egraph_id, false_egraph_id)
    {
        let negated_model_terms: Vec<i32> = negated_model
            .into_iter()
            .map(|x| -solver_state.make_eq(x.0, x.1))
            .collect();
        debug_println!(
            24,
            1,
            "Contradiction found [2] (setting true = false): {:?} [{:?}]",
            negated_model_terms
                .iter()
                .map(|x| solver_state.get_term_from_lit(*x))
                .collect::<Vec<_>>(),
            negated_model_terms
        );
        if is_important(7) {
            for lit in negated_model_terms.clone() {
                debug_println!(7, 4, "{}", solver_state.get_term_from_lit(lit));
            }
        }

        return if let Some(mut constraints) = additional_constraints {
            constraints.push(negated_model_terms);
            Some(constraints)
        } else {
            Some(vec![negated_model_terms])
        };
    }

    debug_println!(
        24,
        0,
        "We have the additional constraints {:?}",
        additional_constraints
    );
    additional_constraints
}

/// Classify a term+sign as an assertion type (equality, disequality, tester, etc.)
pub fn find_if_eq_diseq<'a>(
    term: &'a Term,
    sign: bool,
    solver_state: &'a SolverState,
    level: usize,
    fixed: bool,
) -> Assertion {
    let hash = if !fixed { solver_state.current_hash } else { 0 };
    match term.repr() {
        App(f, t, _)
            if (matches!(f.get_kind(), Some(IdentifierKind::Is(_)))
                || (f.get_kind().is_none() && f.id_str().get().starts_with("is-")))
                && t.len() == 1
                && sign =>
        {
            let ctor_name = if let Some(IdentifierKind::Is(sym)) = f.get_kind() {
                Some(sym.clone())
            } else {
                let name = &f.id_str().get()[3..];
                solver_state
                    .datatype_info
                    .constructors
                    .keys()
                    .find(|k| *k.get() == *name)
                    .cloned()
            };
            if let Some(ctor_name) = ctor_name {
                let inner_term = t[0].clone();
                Assertion::Tester {
                    ctor_name,
                    inner_term,
                    term: term.clone(),
                }
            } else {
                Assertion::Other
            }
        }

        Eq(left, right) => {
            if sign {
                debug_println!(1, 2, "Creating equality assertion");
                Assertion::Equality {
                    t1: left.uid(),
                    t2: right.uid(),
                    level,
                    hash,
                }
            } else {
                debug_println!(1, 2, "Creating disequality assertion");
                Assertion::Disequality {
                    t1: left.uid(),
                    t2: right.uid(),
                    level,
                    hash,
                }
            }
        }
        Distinct(terms) => {
            if sign {
                debug_println!(1, 2, "Creating equality assertion");
                Assertion::Distinct {
                    terms: terms.iter().map(|x| x.uid()).collect(),
                    level,
                    hash,
                }
            } else {
                panic!("We do not currently support the negation of a disstinct")
            }
        }
        Not(inner) => match inner.repr() {
            Eq(left, right) => {
                debug_println!(1, 2, "Creating disequality assertion");
                assert!(sign);
                Assertion::Disequality {
                    t1: left.uid(),
                    t2: right.uid(),
                    level,
                    hash,
                }
            }
            Distinct(_) => {
                panic!("We do not currently support the negation of a distinct")
            }
            _ => {
                debug_println!(0, 2, "Found negation, treating as Other");
                Assertion::Other
            }
        },
        _ => {
            debug_println!(
                0,
                2,
                "Found unsupported operator: {:?}, treating as Other",
                term.repr()
            );
            Assertion::Other
        }
    }
}
