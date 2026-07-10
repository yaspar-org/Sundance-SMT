// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Lazy Z3 arithmetic backend.
//!
//! Design:
//! * Persistent `z3::Solver` lives for the whole search.
//! * Each egraph node with sort Int gets its own Z3 `Int` variable, keyed by
//!   its raw egraph id (NOT its union-find root). We never canonicalise at
//!   encoding time — merges are conveyed to Z3 as explicit `var_a == var_b`
//!   assertions.
//! * Every `z3::Solver::push` is recorded against the current SAT decision
//!   level so that `notify_backtrack(level)` can `pop` the matching count.
//! * Arithmetic literals from CaDiCaL's trail (`notify_assignment`) are
//!   translated once, cached by literal, and pushed with `assert_and_track`
//!   so that an unsat core maps back to SAT literals.
//! * Egraph merges from `Egraph::arithmetic_merge_queue` are drained by the
//!   propagator and pushed here as `Int::eq(var_a, var_b)`.
//! * `check()` runs `solver.check()` and returns either `ArithResult::Unsat`
//!   (with the SAT literals from the unsat core) or `ArithResult::Sat` (with
//!   the current arithmetic-term roots grouped by model value, for the
//!   downstream Nelson-Oppen model-based probe).

use crate::arithmetic::lia::stats::Stats as LiaStats;
use crate::arithmetic::lp::{ArithResult, Coefficient, FunctionType, LinearConstraint};
use crate::debug_println;
use crate::egraphs::traits::EgraphTrait;
use crate::solver_state::SolverState;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::Integer;
use dashu::integer::IBig;
use yaspar_ir::ast::{
    ATerm::{self, App, Global, Not},
    FetchSort, HasArena, Repr,
    alg::Constant as AlgConstant,
};
use z3::{
    SatResult, Solver,
    ast::{Bool, Int},
};

/// Convert a dashu IBig to num::BigInt (Z3 uses num::BigInt).
fn ibig_to_bigint(n: &IBig) -> num::BigInt {
    num::BigInt::parse_bytes(n.to_string().as_bytes(), 10).unwrap()
}

/// Parse a Z3 model value string like "3" or "(- 4)" into an IBig.
fn parse_z3_model_int(s: &str) -> IBig {
    if let Some(inner) = s.strip_prefix("(- ").and_then(|t| t.strip_suffix(')')) {
        -inner.parse::<IBig>().unwrap_or_else(|e| {
            panic!("Failed to parse Z3 model value inner '{inner}' from '{s}': {e}")
        })
    } else {
        s.parse::<IBig>()
            .unwrap_or_else(|e| panic!("Failed to parse Z3 model value '{s}': {e}"))
    }
}

/// State for the lazy Z3 arithmetic backend.
pub struct Z3LazyState {
    /// The persistent Z3 solver.
    solver: Solver,
    /// egraph_id -> its Z3 Int variable. Populated on demand.
    var_map: DeterministicHashMap<u32, Int>,
    /// SAT literal (unsigned, positive) -> its tracker Bool used by
    /// `assert_and_track`, so that an unsat core recovers the literal.
    /// Present iff the literal has been encoded into the solver at least once.
    tracker_by_lit: DeterministicHashMap<i32, Bool>,
    /// tracker string name -> signed SAT literal that produced it. Populated
    /// alongside `tracker_by_lit`; we use `to_string()` to look up in the
    /// unsat core because z3-rs `Bool` doesn't hash by identity.
    lit_by_tracker_name: DeterministicHashMap<String, i32>,
    /// Absolute value of literals for which we've already decided
    /// "not arithmetic" — skip re-parsing on every re-assignment.
    non_arithmetic_lits: DeterministicHashSet<i32>,
    /// Signed literals currently pushed into the persistent Z3 solver.
    /// Prevents duplicate pushes when CaDiCaL notifies the same literal
    /// more than once at the same level (e.g. after simplification).
    active_lits: DeterministicHashSet<i32>,
    /// For each decision level, the signed lits that were pushed at that
    /// level. Used by `notify_backtrack` to remove them from `active_lits`.
    lits_by_level: Vec<Vec<i32>>,
    /// Stack of push counts per decision level. Entry `i` is how many
    /// `z3::push`es we've done at level `i`; on `notify_backtrack(level)`
    /// we pop everything above `level`.
    /// Indexed by decision level; grows as decision level grows.
    push_counts: Vec<u32>,
    /// Definitional pinnings (e.g. `var_5 == 5`, `var_{(+xy)} == var_x + var_y`).
    /// These are theory facts that hold globally, so we replay them as
    /// assumptions on every `check_assumptions` rather than asserting them into
    /// a specific scope (where a later `pop` would erase them).
    pinned_defs: Vec<Bool>,
    /// Current SAT decision level, tracked internally to match the propagator.
    current_level: usize,
    /// Counter used to give each conflict-dump file a unique name when the
    /// `SUNDANCE_CONFLICT_DIR` env var is set.
    conflict_dump_counter: usize,
}

impl Z3LazyState {
    pub fn new() -> Self {
        Self {
            solver: Solver::new(),
            var_map: DeterministicHashMap::new(),
            tracker_by_lit: DeterministicHashMap::new(),
            lit_by_tracker_name: DeterministicHashMap::new(),
            non_arithmetic_lits: DeterministicHashSet::default(),
            active_lits: DeterministicHashSet::default(),
            lits_by_level: vec![Vec::new()],
            push_counts: vec![0],
            pinned_defs: Vec::new(),
            current_level: 0,
            conflict_dump_counter: 0,
        }
    }

    /// Ensure `push_counts` and per-level tracking vectors are indexed up to
    /// `self.current_level`.
    fn ensure_level_slot(&mut self) {
        while self.push_counts.len() <= self.current_level {
            self.push_counts.push(0);
        }
        while self.lits_by_level.len() <= self.current_level {
            self.lits_by_level.push(Vec::new());
        }
    }

    /// Get or create the Z3 `Int` variable for an egraph id, and on first
    /// creation pin it to its term structure (`var_{id} == <constant>` for
    /// numeric constants, `var_{id} == <linear combination in child vars>`
    /// for arithmetic applications like `+ - *`). Uninterpreted apps and
    /// Globals get no pinning — they're left as free Ints.
    ///
    /// Uses `extract_lazy_expression` (no `find()`) so pinnings are stable
    /// across egraph backtracks — merges are conveyed separately via
    /// `drain_merge_queue`.
    ///
    /// Pins are stored in `pinned_defs` and replayed as assumptions on every
    /// `check_assumptions` call, since `Solver::assert`ing them would land
    /// them in the current push scope and get erased on the next `pop`.
    ///
    /// This is the ONLY var-materialization entry point. Every caller that
    /// touches a Z3 var goes through here, so the invariant "any var Z3
    /// sees is already pinned" holds by construction.
    fn var_for(&mut self, egraph_id: u32, solver_state: &mut SolverState) -> Int {
        if let Some(v) = self.var_map.get(&egraph_id) {
            return v.clone();
        }
        let v = Int::new_const(format!("var_{egraph_id}"));
        self.var_map.insert(egraph_id, v.clone());

        let solver_uid = solver_state.to_solver_uid(egraph_id);
        if let Some(expr) = extract_lazy_expression(solver_uid, solver_state) {
            // If the expression is exactly `var_{egraph_id}` (a plain Global
            // or an uninterpreted-function App), skip pinning.
            let is_self_reference = expr.len() == 2
                && expr.get(&Coefficient::Constant) == Some(&IBig::from(0))
                && expr.get(&Coefficient::Term(egraph_id)) == Some(&IBig::from(1));
            if !is_self_reference {
                let mut rhs = Int::from_i64(0);
                let entries: Vec<(Coefficient, IBig)> =
                    expr.iter().map(|(k, v)| (*k, v.clone())).collect();
                for (k, c) in &entries {
                    if let Some(e) = self.coeff_to_z3(k, c, solver_state) {
                        rhs += e;
                    }
                }
                let def = Int::eq(&v, rhs);
                self.pinned_defs.push(def);
                debug_println!(21, 0, "[z3lazy] def var_{}=={:?}", egraph_id, entries);
            }
        }
        v
    }

    /// Translate a coefficient key to a Z3 Int expression scaled by `coeff`.
    /// Uses raw egraph ids as variables — no `find()`. Pins numeric constants.
    fn coeff_to_z3(
        &mut self,
        key: &Coefficient,
        coeff: &IBig,
        solver_state: &mut SolverState,
    ) -> Option<Int> {
        match key {
            Coefficient::Constant => Some(Int::from_big_int(&ibig_to_bigint(coeff))),
            Coefficient::Term(id) => {
                let v = self.var_for(*id, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * v)
            }
            Coefficient::Div(a, b) => {
                let av = self.var_for(*a, solver_state);
                let bv = self.var_for(*b, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * av.div(bv))
            }
            Coefficient::Mod(a, b) => {
                let av = self.var_for(*a, solver_state);
                let bv = self.var_for(*b, solver_state);
                Some(Int::from_big_int(&ibig_to_bigint(coeff)) * av.modulo(bv))
            }
        }
    }

    /// Encode a LinearConstraint as a Z3 Bool.
    fn constraint_to_z3(&mut self, c: &LinearConstraint, solver_state: &mut SolverState) -> Bool {
        let mut left = Int::from_i64(0);
        for (k, v) in &c.left_expr {
            if let Some(e) = self.coeff_to_z3(k, v, solver_state) {
                left += e;
            }
        }
        let mut right = Int::from_i64(0);
        for (k, v) in &c.right_expr {
            if let Some(e) = self.coeff_to_z3(k, v, solver_state) {
                right += e;
            }
        }
        match c.function {
            FunctionType::Leq => Int::le(&left, &right),
            FunctionType::Lt => Int::lt(&left, &right),
            FunctionType::Eq => Int::eq(&left, right),
        }
    }

    /// Try to build a LinearConstraint for a signed SAT literal.
    /// Returns None if the underlying term is not an arithmetic atom.
    /// Uses raw egraph ids (no `find()`) — no additional_constraints are
    /// generated, since egraph merges are conveyed as explicit equalities.
    fn extract_lazy_constraint(
        lit: i32,
        solver_state: &mut SolverState,
    ) -> Option<LinearConstraint> {
        let (term_id, polarity) = solver_state.get_u64_from_lit_with_polarity(lit);
        let term = solver_state.get_term(term_id);
        let (term, polarity) = match term.repr() {
            Not(t) => (t.clone(), !polarity),
            _ => (term, polarity),
        };
        match term.repr() {
            App(identifier, args, _) => {
                if args.len() != 2 {
                    return None;
                }
                // Use the lazy extractor (no find()) so the encoding of a
                // literal is stable — Z3 push/pop mirrors the assignment
                // stack precisely, without depending on egraph state.
                let left_expr = extract_lazy_expression(args[0].uid(), solver_state)?;
                let right_expr = extract_lazy_expression(args[1].uid(), solver_state)?;
                let sym = identifier.0.symbol.as_str();
                let (le, re, func) = match (sym, polarity) {
                    ("<=", true) => (left_expr, right_expr, FunctionType::Leq),
                    ("<=", false) => (right_expr, left_expr, FunctionType::Lt),
                    (">=", true) => (right_expr, left_expr, FunctionType::Leq),
                    (">=", false) => (left_expr, right_expr, FunctionType::Lt),
                    ("<", true) => (left_expr, right_expr, FunctionType::Lt),
                    ("<", false) => (right_expr, left_expr, FunctionType::Leq),
                    (">", true) => (right_expr, left_expr, FunctionType::Lt),
                    (">", false) => (left_expr, right_expr, FunctionType::Leq),
                    _ => return None,
                };
                Some(LinearConstraint::new(le, re, func, vec![]))
            }
            // Equality atoms (positive or negative polarity) are handled by
            // the egraph — positive assertions produce merges that flow through
            // `drain_merge_queue`; negative assertions become egraph
            // disequalities. We intentionally do NOT encode them directly here,
            // so lazy Z3 sees exactly one source of truth per equality.
            _ => None,
        }
    }

    /// Called when the SAT solver enters a new decision level.
    pub fn notify_new_decision_level(&mut self) {
        self.current_level += 1;
        self.ensure_level_slot();
    }

    /// Called on backtrack. Pops all `z3::push`es done at levels > `level`.
    pub fn notify_backtrack(&mut self, level: usize) {
        while self.current_level > level {
            let n = self.push_counts.pop().unwrap_or(0);
            if n > 0 {
                self.solver.pop(n);
            }
            if let Some(lits) = self.lits_by_level.pop() {
                for l in lits {
                    self.active_lits.remove(&l);
                }
            }
            self.current_level -= 1;
        }
        self.ensure_level_slot();
    }

    /// Called for each SAT literal newly assigned by CaDiCaL. If the
    /// literal corresponds to an arithmetic atom, push its constraint into
    /// the persistent solver at the current level (tracked so the unsat
    /// core recovers the literal).
    pub fn on_literal_assignment(&mut self, lit: i32, solver_state: &mut SolverState) {
        let abs_lit = lit.abs();
        if self.non_arithmetic_lits.contains(&abs_lit) {
            return;
        }
        // CaDiCaL may re-notify the same literal (e.g. it appears both as an
        // individual notify_assignment and again in the initial-trail batch).
        // Guard against a duplicate push.
        if self.active_lits.contains(&lit) {
            return;
        }
        let Some(constraint) = Self::extract_lazy_constraint(lit, solver_state) else {
            self.non_arithmetic_lits.insert(abs_lit);
            return;
        };
        let ast = self.constraint_to_z3(&constraint, solver_state);
        let tracker_name = format!("lit_{lit}");
        let tracker = Bool::new_const(tracker_name.clone());
        self.tracker_by_lit.insert(lit, tracker.clone());
        self.lit_by_tracker_name.insert(tracker_name, lit);
        self.ensure_level_slot();
        self.solver.push();
        self.push_counts[self.current_level] += 1;
        self.active_lits.insert(lit);
        self.lits_by_level[self.current_level].push(lit);
        self.solver.assert_and_track(ast, &tracker);
        debug_println!(
            21,
            0,
            "[z3lazy] pushed atom lit={} at level {}",
            lit,
            self.current_level
        );
    }

    /// Drain the egraph's arithmetic merge queue into the persistent Z3 solver.
    /// Each merge becomes `var_a == var_b` asserted at the current level.
    /// `provoker` is the SAT literal (if any) whose `notify_assignment` produced
    /// Drain the egraph's arithmetic merge queue. For each merge `(a, b)`,
    /// allocate the SAT literal for `(= t_a t_b)` via `make_eq`, then push
    /// `var_a == var_b` into Z3 via `assert_and_track` with a tracker keyed
    /// on that literal. Result: each merge is a normal tracked atom, and
    /// Z3's unsat core will blame exactly the merge lits that were actually
    /// used in the conflict — no over-approximation.
    ///
    /// Returns the list of freshly-allocated SAT lits so the caller can
    /// register them as observed with CaDiCaL and the proof tracer.
    pub fn drain_merge_queue(&mut self, solver_state: &mut SolverState) -> Vec<i32> {
        let merges = std::mem::take(&mut solver_state.egraph.arithmetic_merge_queue);
        if merges.is_empty() {
            return Vec::new();
        }
        self.ensure_level_slot();
        let mut new_lits: Vec<i32> = Vec::new();
        for (a, b) in merges {
            // Allocate the SAT literal for the term-level equality (= t_a t_b).
            // If a lit already exists, `make_eq` returns the existing one; if
            // not, it allocates a fresh one. We remember which ones are fresh
            // so the caller can register them with CaDiCaL.
            let was_registered = solver_state.get_term_from_lit_safe(1).is_some(); // dummy — we track via cnf_cache
            let _ = was_registered;
            let lit = solver_state.make_eq(a, b);
            let _abs_lit = lit.abs();
            // Cheap detection: if this abs_lit isn't in tracker_by_lit yet
            // AND isn't in non_arithmetic_lits, it's a candidate new atom.
            // Treat the merge as a positive assignment of that lit — push
            // it via the same code path as any other arithmetic atom.
            let is_new =
                !self.tracker_by_lit.contains_key(&lit) && !self.tracker_by_lit.contains_key(&-lit);
            if is_new {
                new_lits.push(lit);
            }
            // Skip if already asserted (duplicate merge notifications happen
            // when the same union is re-fired during backtrack replay).
            if self.active_lits.contains(&lit) {
                continue;
            }
            // Encode as `var_a == var_b` (matches the atom encoding for
            // `(= t_a t_b)` under our extractor).
            let va = self.var_for(a, solver_state);
            let vb = self.var_for(b, solver_state);
            let ast = Int::eq(&va, vb);
            let tracker_name = format!("lit_{lit}");
            let tracker = Bool::new_const(tracker_name.clone());
            self.tracker_by_lit.insert(lit, tracker.clone());
            self.lit_by_tracker_name.insert(tracker_name, lit);
            self.solver.push();
            self.push_counts[self.current_level] += 1;
            self.active_lits.insert(lit);
            self.lits_by_level[self.current_level].push(lit);
            self.solver.assert_and_track(ast, &tracker);
            debug_println!(
                21,
                0,
                "[z3lazy] pushed egraph merge var_{}==var_{} as lit {} at level {}",
                a,
                b,
                lit,
                self.current_level
            );
        }
        new_lits
    }

    /// Run `solver.check()`. On SAT, group current arithmetic-term roots by
    /// model value so the caller's model-based Nelson-Oppen probe can run.
    /// On UNSAT, translate the unsat core back into SAT literals.
    pub fn check(&mut self, solver_state: &mut SolverState) -> ArithResult {
        debug_println!(21, 0, "[z3lazy] check() at level {}", self.current_level);
        // Ensure every arithmetic-term class root has been introduced to Z3
        // with its definitional equality pinned. If we defer this until the
        // model-evaluation loop below, Z3 has already produced a model
        // without seeing the definitions and the buckets are meaningless.
        let n_arith = solver_state.arithmetic_terms.len();
        for idx in 0..n_arith {
            let term_id = solver_state.arithmetic_terms[idx];
            let egraph_id = solver_state.to_egraph_id(term_id);
            let _ = self.var_for(egraph_id, solver_state);
        }
        // Every arithmetic literal was pushed via `assert_and_track(constraint,
        // tracker)`, which encodes `tracker => constraint`. Z3 would happily
        // satisfy that by picking tracker=false unless we tell it the tracker
        // is true — so we run `check_assumptions` with the currently-active
        // trackers. Include the definitional pinnings too — those live outside
        // any push scope so they'd otherwise be pop'd.
        let mut assumptions: Vec<Bool> = self
            .active_lits
            .iter()
            .filter_map(|lit| self.tracker_by_lit.get(lit).cloned())
            .collect();
        assumptions.extend(self.pinned_defs.iter().cloned());
        match self.solver.check_assumptions(&assumptions) {
            SatResult::Sat => {
                let model = self.solver.get_model().unwrap();
                let mut buckets: DeterministicHashMap<IBig, DeterministicHashSet<u64>> =
                    DeterministicHashMap::new();
                for idx in 0..solver_state.arithmetic_terms.len() {
                    let term_id = solver_state.arithmetic_terms[idx];
                    let egraph_id = solver_state.to_egraph_id(term_id);
                    // Only report one representative per union-find class —
                    // otherwise the model-based probe wastes work merging
                    // pairs that are already equal.
                    if solver_state.egraph.find(egraph_id) != egraph_id {
                        continue;
                    }
                    let v = self.var_for(egraph_id, solver_state);
                    if let Some(val) = model.eval(&v, true) {
                        let ibig = parse_z3_model_int(&val.to_string());
                        buckets.entry(ibig).or_default().insert(term_id);
                    }
                }
                debug_println!(21, 0, "[z3lazy] SAT buckets={:?}", buckets);
                ArithResult::Sat(buckets, LiaStats::new())
            }
            SatResult::Unsat => {
                let core = self.solver.get_unsat_core();
                let mut lits: DeterministicHashSet<i32> = DeterministicHashSet::default();
                for ast in &core {
                    let name = ast.to_string();
                    if let Some(&lit) = self.lit_by_tracker_name.get(&name) {
                        lits.insert(-lit);
                    } else {
                        debug_println!(
                            21,
                            0,
                            "[z3lazy] unsat core contained unknown tracker: {}",
                            name
                        );
                    }
                }
                // Merges are now tracked via `assert_and_track` (see
                // `drain_merge_queue`), so Z3's unsat core cites exactly the
                // merge lits (via `make_eq`-allocated SAT lits) that were
                // actually used in the conflict. No over-approximation needed.
                if lits.is_empty() {
                    // Sanity guard: if no tracked lits appear in the core, the
                    // contradiction lives entirely in pinned defs — a bug.
                    // Fall back to blaming every active lit rather than
                    // reporting unsound `Unsat([])`.
                    lits.extend(self.active_lits.iter().map(|l| -l));
                }
                let conflict: Vec<i32> = lits.into_iter().collect();
                self.print_and_validate_conflict(&conflict, solver_state);
                ArithResult::Unsat(conflict, LiaStats::new())
            }
            SatResult::Unknown => panic!("z3lazy: Z3 returned unknown"),
        }
    }

    /// Print a conflict clause with human-readable term forms. If the env
    /// variable `SUNDANCE_CONFLICT_DIR` is set, dump the negated-clause SMT2
    /// query to a file in that directory for later batch validation via z3.
    ///
    /// A conflict clause `[l1, l2, ...]` means `l1 ∨ l2 ∨ ...` — it's a
    /// valid theory conflict iff `¬l1 ∧ ¬l2 ∧ ...` is unsat.
    fn print_and_validate_conflict(&mut self, clause: &[i32], solver_state: &mut SolverState) {
        // Gated on the `SUNDANCE_CONFLICT_DIR` env var: if unset (the default),
        // this is a no-op. Set it to a directory path to have every arithmetic
        // conflict printed to stderr AND dumped as an SMT2 file in that
        // directory, ready for batch validation via z3.
        let out_dir = match std::env::var("SUNDANCE_CONFLICT_DIR") {
            Ok(d) if !d.is_empty() => d,
            _ => return,
        };

        eprintln!("[z3lazy CONFLICT] clause of {} lits:", clause.len());
        for &lit in clause {
            if let Some(term) = solver_state.get_term_from_lit_safe(lit) {
                eprintln!("  {:5}  =  {}", lit, term);
            } else {
                eprintln!("  {:5}  =  <no term>", lit);
            }
        }

        // Build an SMT2 dump that mirrors the printed conflict — one
        // `(assert ...)` per literal, using each literal's term shape
        // directly, with declare-sort/declare-fun for every symbol used.
        // We do NOT include the pinned defs or the ambient egraph state —
        // the goal is a minimal, human-readable query whose unsat verifies
        // that the conflict clause is a valid theory tautology.
        use std::collections::BTreeSet;
        let mut sorts: BTreeSet<String> = BTreeSet::new();
        let mut funcs: DeterministicHashMap<String, (Vec<String>, String)> =
            DeterministicHashMap::new();
        let mut asserts: Vec<String> = Vec::new();
        // Some conflicts reference datatype constructors/testers/selectors
        // (e.g. `((_ is Foo) x)`, `(Foo/field x)`). Without emitting the full
        // `declare-datatypes`, z3 rejects the dump. Skip validation for those.
        let mut has_datatype_refs = false;

        for &lit in clause {
            let Some(term) = solver_state.get_term_from_lit_safe(-lit) else {
                continue;
            };
            collect_symbols(&term, solver_state, &mut sorts, &mut funcs);
            let s = term.to_string();
            if s.contains("(_ is ") {
                has_datatype_refs = true;
            }
            asserts.push(format!("(assert {})", s));
        }
        if asserts.is_empty() {
            return;
        }
        if has_datatype_refs {
            // Dump would need `declare-datatypes` to be checkable by z3.
            // Skip writing so batch validation doesn't false-flag it.
            return;
        }

        // Bump the global counter (per Z3LazyState) for a unique file name.
        // Include the process PID so parallel Sundance instances don't clash
        // when writing to a shared conflict directory.
        self.conflict_dump_counter += 1;
        let file = format!(
            "{}/pid{}_conflict_{}.smt2",
            out_dir,
            std::process::id(),
            self.conflict_dump_counter
        );

        let mut out = String::new();
        out.push_str(&format!("; conflict clause ({} lits):\n", clause.len()));
        for &lit in clause {
            let term_str = solver_state
                .get_term_from_lit_safe(lit)
                .map(|t| t.to_string())
                .unwrap_or_else(|| "<no term>".to_string());
            out.push_str(&format!(";   {}  =  {}\n", lit, term_str));
        }
        out.push('\n');

        // Sort declarations. Skip built-in sorts (Int, Bool, Real).
        for s in &sorts {
            if s != "Int" && s != "Bool" && s != "Real" {
                out.push_str(&format!("(declare-sort {} 0)\n", s));
            }
        }
        // Function/constant declarations, sorted for stability.
        let mut func_entries: Vec<(&String, &(Vec<String>, String))> = funcs.iter().collect();
        func_entries.sort_by(|a, b| a.0.cmp(b.0));
        for (name, (arg_sorts, ret_sort)) in func_entries {
            if arg_sorts.is_empty() {
                out.push_str(&format!("(declare-const {} {})\n", name, ret_sort));
            } else {
                out.push_str(&format!(
                    "(declare-fun {} ({}) {})\n",
                    name,
                    arg_sorts.join(" "),
                    ret_sort
                ));
            }
        }
        out.push('\n');
        for a in &asserts {
            out.push_str(a);
            out.push('\n');
        }
        out.push_str("(check-sat)\n");

        if let Err(e) = std::fs::write(&file, &out) {
            eprintln!("[z3lazy] failed to write conflict dump {file}: {e}");
        }
    }
}

impl Default for Z3LazyState {
    fn default() -> Self {
        Self::new()
    }
}

/// Walk `term` and record every free symbol (Global constant or App head)
/// into `funcs` and every non-built-in sort into `sorts`. Used by the
/// conflict-dump code to emit `declare-sort`/`declare-fun` headers.
fn collect_symbols(
    term: &yaspar_ir::ast::Term,
    solver_state: &mut SolverState,
    sorts: &mut std::collections::BTreeSet<String>,
    funcs: &mut DeterministicHashMap<String, (Vec<String>, String)>,
) {
    use yaspar_ir::ast::ATerm::{And, Distinct, Eq as EqT, Implies, Ite, Not as NotT, Or, Xor};
    fn record_sort(s: &str, sorts: &mut std::collections::BTreeSet<String>) {
        sorts.insert(s.to_string());
    }
    match term.repr() {
        Global(qi, _) => {
            let name = qi.0.symbol.to_string();
            let ret_sort = term.get_sort(solver_state.context.arena()).to_string();
            record_sort(&ret_sort, sorts);
            funcs.entry(name).or_insert((Vec::new(), ret_sort));
        }
        App(qi, args, _) => {
            let head = qi.0.symbol.to_string();
            // Skip built-in operators — SMT-LIB knows +, -, *, div, mod,
            // <, <=, >, >=, =, and, or, not, ite, etc.
            let builtin = matches!(
                head.as_str(),
                "+" | "-"
                    | "*"
                    | "div"
                    | "mod"
                    | "<"
                    | "<="
                    | ">"
                    | ">="
                    | "="
                    | "and"
                    | "or"
                    | "not"
                    | "xor"
                    | "=>"
                    | "ite"
                    | "distinct"
                    | "true"
                    | "false"
            );
            let ret_sort = term.get_sort(solver_state.context.arena()).to_string();
            record_sort(&ret_sort, sorts);
            let arg_sorts: Vec<String> = args
                .iter()
                .map(|a| {
                    let s = a.get_sort(solver_state.context.arena()).to_string();
                    record_sort(&s, sorts);
                    s
                })
                .collect();
            if !builtin && !funcs.contains_key(&head) {
                funcs.insert(head, (arg_sorts, ret_sort));
            }
            for a in args {
                collect_symbols(a, solver_state, sorts, funcs);
            }
        }
        EqT(a, b) => {
            collect_symbols(a, solver_state, sorts, funcs);
            collect_symbols(b, solver_state, sorts, funcs);
        }
        NotT(t) => collect_symbols(t, solver_state, sorts, funcs),
        And(items) | Or(items) | Xor(items) | Distinct(items) => {
            for t in items {
                collect_symbols(t, solver_state, sorts, funcs);
            }
        }
        Implies(pre, post) => {
            for t in pre {
                collect_symbols(t, solver_state, sorts, funcs);
            }
            collect_symbols(post, solver_state, sorts, funcs);
        }
        Ite(c, t, e) => {
            collect_symbols(c, solver_state, sorts, funcs);
            collect_symbols(t, solver_state, sorts, funcs);
            collect_symbols(e, solver_state, sorts, funcs);
        }
        _ => {}
    }
}

/// Version of `extract_linear_expression` that never calls `egraph.find()`.
/// Returns None if the term is not an arithmetic term of a supported shape.
/// Every `Coefficient::Term(id)` in the returned map refers to the term's
/// own raw egraph id — merges are conveyed to Z3 separately.
fn extract_lazy_expression(
    term_id: u64,
    solver_state: &mut SolverState,
) -> Option<DeterministicHashMap<Coefficient, Integer>> {
    let term = solver_state.get_term(term_id);
    let mut expr: DeterministicHashMap<Coefficient, Integer> = DeterministicHashMap::new();
    expr.insert(Coefficient::Constant, IBig::from(0));
    match term.repr() {
        ATerm::Constant(c, _) => {
            if let AlgConstant::Numeral(num) = c
                && let Ok(value) = num.to_string().parse::<Integer>()
            {
                *expr.get_mut(&Coefficient::Constant).unwrap() = value;
            }
            Some(expr)
        }
        Global(..) => {
            expr.insert(
                Coefficient::Term(solver_state.to_egraph_id(term_id)),
                IBig::from(1),
            );
            Some(expr)
        }
        App(identifier, args, _) => match identifier.0.symbol.as_str() {
            "+" => {
                for arg in args.iter() {
                    let sub = extract_lazy_expression(arg.uid(), solver_state)?;
                    for (k, c) in sub {
                        if k == Coefficient::Constant {
                            *expr.get_mut(&Coefficient::Constant).unwrap() += c;
                        } else {
                            *expr.entry(k).or_insert(IBig::from(0)) += c;
                        }
                    }
                }
                Some(expr)
            }
            "-" => {
                if args.is_empty() {
                    return None;
                }
                if args.len() == 1 {
                    let sub = extract_lazy_expression(args[0].uid(), solver_state)?;
                    for (k, c) in sub {
                        expr.insert(k, -c);
                    }
                    Some(expr)
                } else {
                    let first = extract_lazy_expression(args[0].uid(), solver_state)?;
                    for (k, c) in first {
                        if k == Coefficient::Constant {
                            *expr.get_mut(&Coefficient::Constant).unwrap() += c;
                        } else {
                            *expr.entry(k).or_insert(IBig::from(0)) += c;
                        }
                    }
                    for arg in args.iter().skip(1) {
                        let sub = extract_lazy_expression(arg.uid(), solver_state)?;
                        for (k, c) in sub {
                            if k == Coefficient::Constant {
                                *expr.get_mut(&Coefficient::Constant).unwrap() -= c;
                            } else {
                                *expr.entry(k).or_insert(IBig::from(0)) -= c;
                            }
                        }
                    }
                    Some(expr)
                }
            }
            "*" => {
                if args.len() != 2 {
                    return None;
                }
                let left = extract_lazy_expression(args[0].uid(), solver_state)?;
                let right = extract_lazy_expression(args[1].uid(), solver_state)?;
                if left.len() == 1 && left.contains_key(&Coefficient::Constant) {
                    let cst = left[&Coefficient::Constant].clone();
                    for (k, c) in right {
                        expr.insert(k, &cst * c);
                    }
                    Some(expr)
                } else if right.len() == 1 && right.contains_key(&Coefficient::Constant) {
                    let cst = right[&Coefficient::Constant].clone();
                    for (k, c) in left {
                        expr.insert(k, &cst * c);
                    }
                    Some(expr)
                } else {
                    // Nonlinear — treat the whole App as an opaque term.
                    let id = solver_state.to_egraph_id(term_id);
                    expr.insert(Coefficient::Term(id), IBig::from(1));
                    Some(expr)
                }
            }
            "div" => {
                if args.len() != 2 {
                    return None;
                }
                let a = solver_state.to_egraph_id(args[0].uid());
                let b = solver_state.to_egraph_id(args[1].uid());
                expr.insert(Coefficient::Div(a, b), IBig::from(1));
                Some(expr)
            }
            "mod" => {
                if args.len() != 2 {
                    return None;
                }
                let a = solver_state.to_egraph_id(args[0].uid());
                let b = solver_state.to_egraph_id(args[1].uid());
                expr.insert(Coefficient::Mod(a, b), IBig::from(1));
                Some(expr)
            }
            _ => {
                // Uninterpreted function application — treat as opaque.
                let id = solver_state.to_egraph_id(term_id);
                expr.insert(Coefficient::Term(id), IBig::from(1));
                Some(expr)
            }
        },
        _ => {
            let id = solver_state.to_egraph_id(term_id);
            expr.insert(Coefficient::Term(id), IBig::from(1));
            Some(expr)
        }
    }
}
