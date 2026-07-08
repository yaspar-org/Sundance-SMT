// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Entry point for the LIA mixed integer arithmetic solver

use crate::arithmetic::incremental::{AssertOutcome, CheckResult, IncrementalArithSolver};
use crate::arithmetic::lia::config::SolverConfig;
use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::frontend;
use crate::arithmetic::lia::linear_system::{Constraint, LinearSystem, Mon, Rel};
use crate::arithmetic::lia::solver_result::SolverDecision;
use crate::arithmetic::lia::variables::{Var, VarType};
use crate::arithmetic::lp::{
    ArithResult, Coefficient, FunctionType, FunctionType::*, LinearConstraint,
    extract_constraint_from_term, extract_linear_constraints, extract_linear_expression,
};
use crate::debug_println;
use crate::egraphs::EgraphTrait;
use crate::solver_state::SolverState;
use crate::utils::{DeterministicHashMap, DeterministicHashSet};
use dashu::{Integer, Rational};
use std::collections::HashMap;

pub fn check_integer_constraints_satisfiable_lia(
    terms: &[i32],
    // TODO: lialp: check that taking egraph mutable is okay
    solver_state: &mut SolverState,
) -> ArithResult {
    let (constraints, arithmetic_literals) = extract_linear_constraints(terms, solver_state);

    if constraints.is_empty() && arithmetic_literals.is_empty() {
        return ArithResult::None; // No constraints mean trivially satisfiable
    }

    debug_println!(21, 4, "trying to solve with constraints: {:?}", constraints);
    debug_println!(21, 4, "and arithmetic literals {:?}", arithmetic_literals);

    let mut var_map = DeterministicHashMap::new();

    // Create a context for the internal arithmetic solver then build it up
    let mut ctx = ConvContext::new();
    let mut roots = vec![];
    // For each var we create in the arithmetic solver, track the literals that were used to justify
    // it. This is used later for translating an "infeasible" outcome into an unsat core.
    let mut slack_to_lits: HashMap<Var, Vec<i32>> = HashMap::new();

    for idx in 0..solver_state.arithmetic_terms.len() {
        let term_id = solver_state.arithmetic_terms[idx];
        let egraph_id = solver_state.to_egraph_id(term_id);
        if solver_state.egraph.find(egraph_id) == egraph_id {
            let (expr, additional_constraints) = extract_linear_expression(term_id, solver_state);
            let root_var = *var_map.entry(egraph_id).or_insert_with(|| {
                ctx.allocate_var(&format!("!ext_var_{}", egraph_id), VarType::Int)
            });
            roots.push((term_id, root_var));

            // We have "root_var = expr," make it into "root_var - expr = 0"
            let (mut monomials, constant) =
                expr_to_monomials(&expr, -Rational::ONE, &mut var_map, &mut ctx);
            monomials.insert(0, Mon::new(Rational::ONE, root_var));

            let slack =
                ctx.allocate_var(&format!("!ext_slack_var_root_{}", term_id), VarType::Real);
            ctx.push_relation(Rel::mk_eq(monomials, constant), slack);
            slack_to_lits.insert(slack, additional_constraints);
        }
    }

    for (constraint_idx, constraint) in constraints.iter().enumerate() {
        debug_println!(4, 0, "WE ARE IN ARITH CHECK: Constraint: {:?}", constraint);
        // We have  "left_expr REL right_expr," make it into "(left_expr - right_expr) REL 0"
        let (mut constr_monomials, mut constant) =
            expr_to_monomials(&constraint.left_expr, Rational::ONE, &mut var_map, &mut ctx);
        let (rhs_monomials, rhs_constant) = expr_to_monomials(
            &constraint.right_expr,
            -Rational::ONE,
            &mut var_map,
            &mut ctx,
        );
        constr_monomials.extend(rhs_monomials);
        constant += rhs_constant;

        let rel = match &constraint.function {
            Leq => Rel::mk_le(constr_monomials, constant),
            Lt => Rel::mk_lt(constr_monomials, constant),
            Eq => Rel::mk_eq(constr_monomials, constant),
        };

        let slack = ctx.allocate_var(
            &format!("!ext_slack_constraint_{}", constraint_idx),
            VarType::Real,
        );
        ctx.push_relation(rel, slack);

        let mut lits = constraint.additional_constraint.clone().unwrap_or_default();
        lits.push(arithmetic_literals[constraint_idx]);
        slack_to_lits.insert(slack, lits);
    }

    match frontend::solve_ctx_raw(&mut ctx, &SolverConfig::default()) {
        Ok(ret) => {
            debug_println!(25, 4, "lia::frontend: stats: {:?}", ret.stats);
            let stats = ret.stats;
            match ret.decision {
                SolverDecision::FEASIBLE(assignment) => {
                    let mut model_hashmap: DeterministicHashMap<i64, DeterministicHashSet<u64>> =
                        DeterministicHashMap::new();
                    for (term_id, root_var) in &roots {
                        if let Some(value) = assignment.get(root_var) {
                            let val_i64: i64 =
                                value.to_int().value().try_into().unwrap_or(i64::MAX);
                            model_hashmap.entry(val_i64).or_default().insert(*term_id);
                        }
                    }
                    ArithResult::Sat(model_hashmap, stats)
                }
                SolverDecision::INFEASIBLE(conflict) => {
                    let unsat_core_literals: Vec<i32> = conflict
                        .iter()
                        .flat_map(|var| slack_to_lits.get(var).into_iter().flatten().copied())
                        .collect();
                    debug_println!(21, 4, "LIA: Unsat core literals: {:?}", unsat_core_literals);
                    ArithResult::Unsat(unsat_core_literals, stats)
                }
                SolverDecision::UNKNOWN => ArithResult::None,
            }
        }
        Err(e) => panic!("lialp: unexpected error: {e:?}"),
    }
}

/// Incremental entry point: check arithmetic satisfiability of `terms` against the persistent
/// [`IncrementalArithSolver`] held on `solver_state` (Stage 7 of the incremental-arithmetic
/// plan).
///
/// Semantics mirror [`check_integer_constraints_satisfiable_lia`]: `terms` is the SAT model
/// slice CaDiCaL hands to `cb_check_found_model`, and the return value is an [`ArithResult`]
/// suitable for the propagator's existing dispatch (`Unsat` → conflict clause pushed into
/// `disequalities`, `Sat` → drives the Nelson-Oppen splitting loop, `None` → skip).
///
/// The protocol on each call is:
/// 1. Open a fresh LP scope (`push`) — every bound asserted in this call is scoped to it.
/// 2. For every literal in `terms`, `assert_literal` on the persistent solver. Non-arithmetic
///    literals return `None` and are skipped; arithmetic ones tighten the pre-registered
///    slack bound. An assert-time bound-vs-bound conflict latches on the solver so `check()`
///    still reports it.
/// 3. `check()` runs a full simplex + branch-and-bound at the current bound set.
/// 4. `pop` the scope — bounds asserted this call are discarded so the *next* call starts
///    clean.
///
/// Optimising away the pop-and-re-assert (an incremental *diff* against the previous model)
/// is a Stage 8 optimisation; the prototype does the simplest correct thing.
///
/// Panics if `solver_state.incremental_arith` is `None` (the CLI dispatcher must only route
/// this variant when the solver has been built by `main.rs`).
pub fn check_integer_constraints_satisfiable_incremental(
    terms: &[i32],
    solver_state: &mut SolverState,
) -> ArithResult {
    // Move the incremental solver out temporarily to avoid tangled borrows against
    // `solver_state` (assert_literal takes `&mut IncrementalArithSolver`, and nothing in the
    // protocol needs `solver_state` after the model literals are copied out).
    let mut solver = solver_state
        .incremental_arith
        .take()
        .expect("check_integer_constraints_satisfiable_incremental: no incremental solver on SolverState");

    debug_println!(
        21,
        4,
        "incremental: check_integer_constraints_satisfiable_incremental with {} model literals",
        terms.len()
    );

    let level = solver.push();

    // Lazily register any arithmetic atoms that weren't in the static builder's atom set.
    // These are typically Nelson-Oppen splitting clauses (`(< a b) ∨ (> a b) ∨ (= a b)`)
    // whose disjuncts didn't exist in `cnf_cache.var_map` when `build_incremental_solver`
    // ran — they were added at runtime by the propagator after the LP model produced them.
    //
    // We always canonicalize on the *positive* SAT literal (the one that appears in
    // `cnf_cache.var_map`). Both `+pos_lit` and `-pos_lit` are registered together via
    // `register_atom_dynamic`, matching the static builder's convention.
    for &lit in terms {
        if solver.atom_for_literal(lit).is_some() || solver.atom_for_literal(-lit).is_some() {
            continue;
        }
        let (uid, _polarity) = solver_state.get_u64_from_lit_with_polarity(lit);
        // Extract with polarity=true to get the atom's own (positive) constraint.
        let Some(constraint) = extract_constraint_from_term(uid, true, solver_state) else {
            continue; // not an arithmetic atom (bool literal, quantifier, etc.)
        };
        let pos_lit = solver_state.get_lit_from_u64(uid);
        // Translate the LinearConstraint's monomials into LRA-level `Mon<Rational>` using
        // the solver's persistent term_var_map. If any referenced term isn't in the LP,
        // skip — that would mean the atom mentions a term the static builder never saw,
        // which shouldn't happen for NO clauses but might for e.g. quantifier bodies
        // touching new Int terms; deferring those is safer than fabricating fresh Vars.
        let mut monomials: Vec<crate::arithmetic::lia::linear_system::Mon<Rational>> = Vec::new();
        let mut constant = Rational::ZERO;
        let mut skip = false;
        for (coeff_kind, int_coeff) in constraint.left_expr.iter() {
            let rc = Rational::from(int_coeff.clone());
            match coeff_kind {
                Coefficient::Term(id) => match solver.var_for_egraph_id(*id) {
                    Some(v) => {
                        monomials.push(crate::arithmetic::lia::linear_system::Mon::new(rc, v));
                    }
                    None => {
                        skip = true;
                        break;
                    }
                },
                Coefficient::Constant => constant += -&rc,
            }
        }
        if skip {
            continue;
        }
        for (coeff_kind, int_coeff) in constraint.right_expr.iter() {
            let rc = Rational::from(int_coeff.clone());
            match coeff_kind {
                Coefficient::Term(id) => match solver.var_for_egraph_id(*id) {
                    Some(v) => {
                        monomials.push(crate::arithmetic::lia::linear_system::Mon::new(-rc, v));
                    }
                    None => {
                        skip = true;
                        break;
                    }
                },
                Coefficient::Constant => constant += rc,
            }
        }
        if skip {
            continue;
        }
        // Combine duplicate-var monomials before pushing so the add_slack_row path
        // never sees a repeated variable (same reason we call combine_terms in the
        // builder — repeat vars corrupt the tableau row).
        let combined = crate::arithmetic::lia::linear_system::combine_terms_helper(&monomials);
        let pos_constraint = match constraint.function {
            FunctionType::Leq => Constraint::Le,
            FunctionType::Lt => Constraint::Lt,
            FunctionType::Eq => Constraint::Eq,
        };
        debug_println!(
            21,
            4,
            "incremental: lazy-registering atom pos_lit={} constraint={:?} monomials={:?} constant={}",
            pos_lit,
            pos_constraint,
            combined,
            constant
        );
        solver.register_atom_dynamic(pos_lit, combined, constant, pos_constraint);
    }

    let mut early_conflict = false;
    for &lit in terms {
        // Keep asserting the rest even after a conflict so `collect_core` sees all
        // justifying atoms; the latched conflict on the solver ensures `check()` still
        // returns Unsat.
        if let Some(AssertOutcome::Conflict) = solver.assert_literal(lit) {
            early_conflict = true;
        }
    }

    // Convey egraph-implied equalities among arithmetic terms into the LP as bounds on
    // fresh equality slacks (Stage 6 / Stage 7 gap). The one-shot path handles this
    // implicitly because `extract_linear_expression` calls `egraph.find` *at every
    // check*, folding congruent terms like `f(x)` and `f(y)` (once `x ≡ y` is asserted)
    // to a single LP `Var`. The incremental path allocates one `Var` per arithmetic
    // term at build time and never re-keys, so without this loop the LP would treat
    // `f(x)` and `f(y)` as independent variables and miss the derived constraint.
    //
    // Approach: group `arithmetic_terms` by their current egraph root; for each
    // multi-term group, `assert_equality` the pairwise equalities into the incremental
    // solver, with the egraph's `explain_equality` translated to SAT literals as
    // justification so any unsat core conveys the responsible atom-level equalities.
    let mut root_groups: DeterministicHashMap<u32, Vec<u64>> = DeterministicHashMap::new();
    for &term_id in &solver_state.arithmetic_terms {
        let egraph_id = solver_state.to_egraph_id(term_id);
        let root = solver_state.egraph.find(egraph_id);
        root_groups.entry(root).or_default().push(term_id);
    }
    for (_root, group) in root_groups {
        if group.len() < 2 {
            continue;
        }
        let anchor = group[0];
        let anchor_egraph = solver_state.to_egraph_id(anchor);
        let anchor_var = match solver.var_for_term(anchor) {
            Some(v) => v,
            None => continue, // anchor isn't in the LP; nothing to bind
        };
        for &other in &group[1..] {
            let other_var = match solver.var_for_term(other) {
                Some(v) => v,
                None => continue,
            };
            let other_egraph = solver_state.to_egraph_id(other);
            // `explain_equality` returns a list of egraph-level assertions whose
            // conjunction implies `anchor ≡ other`; each translated `-make_eq(a, b)`
            // literal is the "negation of an assertion that made these two terms
            // egraph-equal" — the same convention the one-shot path uses when it
            // folds `additional_constraint` into the unsat core.
            let justification: Vec<i32> = solver_state
                .egraph
                .explain_equality(anchor_egraph, other_egraph)
                .map(|eqs| {
                    eqs.into_iter()
                        .map(|(a, b)| -solver_state.make_eq(a, b))
                        .collect()
                })
                .unwrap_or_default();
            debug_println!(
                21,
                4,
                "incremental: egraph-implied equality {:?}({}) ≡ {:?}({}) justification={:?}",
                anchor_var,
                anchor,
                other_var,
                other,
                justification
            );
            if let AssertOutcome::Conflict =
                solver.assert_equality(anchor_var, other_var, justification)
            {
                early_conflict = true;
            }
        }
    }

    let result = solver.check();
    let arith_result = match result {
        CheckResult::Sat { model, stats } => ArithResult::Sat(model, stats),
        CheckResult::Unsat {
            core_literals,
            stats,
        } => {
            debug_println!(
                21,
                4,
                "incremental: Unsat core literals: {:?} (early_conflict={})",
                core_literals,
                early_conflict
            );
            ArithResult::Unsat(core_literals, stats)
        }
        CheckResult::Unknown(_stats) => ArithResult::None,
    };

    // Pop the scope so every bound asserted in this call is discarded; the next call starts
    // from the base bound set (same as the one-shot path's fresh-rebuild semantics).
    solver.pop(level);

    // Put the solver back before returning.
    solver_state.incremental_arith = Some(solver);
    arith_result
}

/// Map the extraction-layer [`FunctionType`] to the linear-system [`Constraint`] used for a
/// *positive* literal. The extraction always normalizes to `left REL right` with `REL` one of
/// `<=`, `<`, `=` (`>=`/`>` are folded into `<=`/`<` by swapping sides), so only these three
/// cases arise.
fn function_to_constraint(f: &FunctionType) -> Constraint {
    match f {
        Leq => Constraint::Le,
        Lt => Constraint::Lt,
        Eq => Constraint::Eq,
    }
}

/// Build a persistent [`IncrementalArithSolver`] with a **static tableau** covering every
/// arithmetic atom in the formula (Stage 2 of the incremental-arithmetic plan).
///
/// Unlike [`check_integer_constraints_satisfiable_lia`], which rebuilds a context + tableau
/// from the *current* SAT model on every call, this walks the full, up-front atom set once:
///
/// - definitional rows `root_var - expr = 0` for each egraph-root arithmetic term (mirrors
///   `check_integer_constraints_satisfiable_lia`, but done once);
/// - one slack per comparison atom, its relation pushed with the atom's threshold as the
///   relation constant. Slacks are built **unbounded** (`to_lra_solver(false, …)`): the bound
///   direction is chosen at assert time, so a single slack serves both polarities of the atom.
///
/// Both `+lit` (the relation) and `-lit` (the negated relation, via [`Constraint::negate`];
/// equality negation is deferred to Nelson-Oppen, matching the one-shot path) are registered
/// against that slack.
///
/// This does **not** touch the live solve path; it is exercised in isolation and against the
/// one-shot path as a differential check (Stage 8).
pub fn build_incremental_solver(solver_state: &mut SolverState) -> IncrementalArithSolver {
    let mut ctx = ConvContext::new();
    // egraph-var-id -> the Var allocated for that arithmetic subterm.
    //
    // Keying: `to_egraph_id(term_id)` is a stable bimap (`solver_state.rs:291`), so this
    // map's keys are *not* affected by egraph merges — same term_id always maps to the same
    // `Var`. `extract_linear_expression` uses `egraph.find` internally for uninterpreted
    // App / fallthrough cases (`lp.rs:427,452`), and the incremental solver relies on that
    // finding being deterministic per (term, egraph-state-at-build-time). Since the builder
    // runs against the pristine pre-search egraph, `find` is the identity here, so the
    // returned `Coefficient::Term(id)` is effectively the same as `to_egraph_id(term_id)`
    // for the roots we care about. Stage 6 wants this property: `Var`s never re-key across
    // subsequent egraph merges, so egraph-implied equalities are conveyed via assertable
    // bounds (`assert_equality`) instead of by rewriting the LP.
    let mut var_map: DeterministicHashMap<u32, Var> = DeterministicHashMap::new();

    // 1. Definitional rows for every arithmetic term (Stage 6): `var_t - expr = 0`.
    //    Pre-Stage-6 skipped terms `t` where `find(t) != t`, losing the definitional row for
    //    the non-root member of any pre-search merge. That skip is gone: every arithmetic
    //    term contributes its own row, and any equality between two terms is represented
    //    downstream as a bound on a fresh slack (`IncrementalArithSolver::assert_equality`).
    //    Iterate a copy of the term list to avoid borrow conflicts with extraction. Also
    //    collect (term_id, root_var) pairs to register as roots for NO model translation.
    let arithmetic_terms = solver_state.arithmetic_terms.clone();
    let mut root_pairs: Vec<(u64, Var)> = Vec::new();
    // Definitional-slack bookkeeping. The definitional rows encode
    // `root_var + Σ(-expr_terms) = constant`, but we pass `relation_bounds=false`
    // to `to_lra_solver` below (atoms need unbounded slacks so `assert_atom` can
    // choose their direction). Passing `false` drops the RHS `constant` on the
    // floor for *every* row — atom rows want that behaviour, but the definitional
    // rows must keep it or a term like the numeral `1` is left free to take any
    // value. So we collect `(slack, constant)` here and assert `slack = constant`
    // permanently on the LRA after it's built.
    let mut definitional_bounds: Vec<(Var, Rational)> = Vec::new();
    for term_id in arithmetic_terms {
        let egraph_id = solver_state.to_egraph_id(term_id);
        let (expr, _additional) = extract_linear_expression(term_id, solver_state);
        let root_var = *var_map
            .entry(egraph_id)
            .or_insert_with(|| ctx.allocate_var(&format!("!ext_var_{}", egraph_id), VarType::Int));
        root_pairs.push((term_id, root_var));

        let (mut monomials, constant) =
            expr_to_monomials(&expr, -Rational::ONE, &mut var_map, &mut ctx);
        monomials.insert(0, Mon::new(Rational::ONE, root_var));
        let slack = ctx.allocate_var(&format!("!ext_slack_var_root_{}", term_id), VarType::Real);
        // Normalize the row before pushing. `expr_to_monomials` can emit multiple
        // `Mon`s on the same `Var` (e.g. a definitional row for a trivially-cyclic
        // expression like `V_v - V_v = 0`, which produces `[+V_v, -V_v]`). The
        // `to_lra_solver` path assigns row coefficients with `row[col] = coeff`
        // instead of accumulating, so a repeated variable would overwrite an earlier
        // coefficient — corrupting the row's meaning (e.g. `slack = 0` becomes
        // `slack = -V_v` in the tableau). `combine_terms` merges duplicates. The
        // one-shot path is safe because `preprocess::preprocess` normalizes every
        // relation; the incremental build path skips preprocess (by design — Stage 6
        // decision to disable eq-elimination) and must therefore normalize here.
        let mut rel = Rel::mk_eq(monomials, constant.clone());
        rel.combine_terms();
        ctx.push_relation(rel, slack);
        definitional_bounds.push((slack, constant));
    }

    // 2. Enumerate all arithmetic comparison atoms once. `var_map` in the CNF cache holds every
    //    atom's uid -> literal. Sort the uids so atom/slack allocation order is deterministic.
    let mut atom_uids: Vec<u64> = solver_state.cnf_cache.var_map.keys().copied().collect();
    atom_uids.sort_unstable();

    // Collect (uid, lit, LinearConstraint) first so all &mut solver_state extraction is done
    // before we start borrowing ctx/var_map mutably alongside the registry.
    let mut atoms: Vec<(i32, LinearConstraint)> = Vec::new();
    for uid in atom_uids {
        let lit = solver_state.get_lit_from_u64(uid);
        // Interpret the atom positively; `extract_constraint_from_term` returns Some exactly for
        // the arithmetic comparisons `<=`, `<`, `>=`, `>`, `=`.
        if let Some(constraint) = extract_constraint_from_term(uid, true, solver_state) {
            atoms.push((lit, constraint));
        }
    }

    let mut incremental_pending: Vec<(i32, Var, Constraint, Rational)> = Vec::new();
    for (idx, (lit, constraint)) in atoms.into_iter().enumerate() {
        // (left_expr - right_expr) REL 0, exactly as the one-shot path builds it.
        let (mut monomials, mut constant) =
            expr_to_monomials(&constraint.left_expr, Rational::ONE, &mut var_map, &mut ctx);
        let (rhs_monomials, rhs_constant) =
            expr_to_monomials(&constraint.right_expr, -Rational::ONE, &mut var_map, &mut ctx);
        monomials.extend(rhs_monomials);
        constant += rhs_constant;

        let pos_constraint = function_to_constraint(&constraint.function);
        let mut rel = match pos_constraint {
            Constraint::Le => Rel::mk_le(monomials, constant.clone()),
            Constraint::Lt => Rel::mk_lt(monomials, constant.clone()),
            Constraint::Eq => Rel::mk_eq(monomials, constant.clone()),
            // function_to_constraint only yields Le/Lt/Eq
            _ => unreachable!("unexpected positive constraint from function_to_constraint"),
        };
        // Merge duplicate-variable monomials before pushing (see note above the
        // definitional row's `combine_terms` — the atom row `left_expr - right_expr
        // REL 0` can put the same var on both sides, e.g. `(= v v)` yields
        // `[+V_v, -V_v]`).
        rel.combine_terms();
        let slack = ctx.allocate_var(&format!("!ext_slack_atom_{}", idx), VarType::Real);
        ctx.push_relation(rel, slack);

        // The threshold for the slack bound is the relation constant.
        incremental_pending.push((lit, slack, pos_constraint, constant));
    }

    // 2b. Ensure every Var in `var_map` appears as a non-basic variable in the LRA.
    //     `to_lra_solver` only creates non-basic columns for Vars that appear in at least
    //     one relation's monomials (via `var_id_set`). A Var allocated for a bare Global
    //     like `x` whose definitional row `[+V_x, -V_x]` combine_terms to `[]` would
    //     otherwise be absent from the LRA — making later `register_var_equality(V_x, ...)`
    //     panic on "unknown variable". Fix: for each Var in var_map not yet referenced in
    //     any relation, push a trivial identity relation `V = 0` (an unbounded slack with a
    //     single-monomial row referencing the Var). The `0` constant is discarded (we pass
    //     `relation_bounds=false`), and the row `slack = V` just establishes the variable as
    //     a non-basic column with an assignment. The slack is unbounded so it doesn't
    //     constrain anything.
    {
        let referenced: std::collections::HashSet<Var> = ctx
            .get_relations()
            .flat_map(|(rel, _)| rel.terms_ref().iter().map(|m| m.var()))
            .collect();
        for v in var_map.values() {
            if !referenced.contains(v) {
                let slack = ctx.allocate_var(
                    &format!("!ext_slack_anchor_{:?}", v),
                    VarType::Real,
                );
                let rel = Rel::mk_eq(
                    vec![Mon::new(Rational::ONE, *v)],
                    Rational::ZERO,
                );
                ctx.push_relation(rel, slack);
                // Pin the anchor slack to 0 permanently. The row is `slack = V`, so
                // `slack = 0` forces `V = 0`. But we DON'T want to force V to 0 — we
                // just want V to exist as a non-basic column! So we leave the slack
                // unbounded (no entry in `definitional_bounds`). The variable starts at 0
                // and will be moved by subsequent atom assertions.
            }
        }
    }

    // 3. Build the LRA solver with unbounded slacks (bounds are asserted incrementally).
    //
    // `to_lra_solver(false, ...)` intentionally leaves every basic slack unbounded so
    // atom slacks can have their bound direction chosen at assert time. But that also
    // strips the RHS constant from *definitional* rows (their constant is not baked
    // into the tableau — it's supposed to live in the slack's bound). Immediately
    // after LRA construction we pin each definitional slack to `slack = constant`
    // permanently. These bounds are asserted at the base scope (level 0) and never
    // retracted, so subsequent push/pop cycles don't disturb them.
    let mut lra = LinearSystem::new(ctx)
        .to_lra_solver(false, &SolverConfig::default())
        .expect("build_incremental_solver: failed to build LRA solver");
    for (slack, constant) in &definitional_bounds {
        let bound = crate::arithmetic::lia::qdelta::QDelta::from(constant.clone());
        // Pin `slack = constant` by asserting both bounds. Slack was created
        // unbounded, so neither assertion can widen an existing bound.
        lra.assert_lower(slack, &bound)
            .expect("build_incremental_solver: assert_lower on definitional slack failed");
        lra.assert_upper(slack, &bound)
            .expect("build_incremental_solver: assert_upper on definitional slack failed");
    }
    let mut solver = IncrementalArithSolver::new(lra, SolverConfig::default());

    // 4. Register both polarities of each atom against its slack.
    for (lit, slack, pos_constraint, threshold) in incremental_pending {
        solver.register_literal_atom(lit, slack, pos_constraint, threshold.clone());
        if let Some(neg_constraint) = pos_constraint.negate() {
            solver.register_literal_atom(-lit, slack, neg_constraint, threshold);
        }
    }

    // 5. Register root (term_id, root_var) pairs for NO model translation.
    for (term_id, root_var) in root_pairs {
        solver.register_root(term_id, root_var);
    }

    // 6. Populate the persistent term_var_map so `register_atom_dynamic` can translate
    //    monomials for atoms introduced at check time (e.g. NO splitting clauses).
    for (egraph_id, v) in var_map.iter() {
        solver.register_term_var(*egraph_id, *v);
    }

    solver
}

pub(crate) fn expr_to_monomials(
    expr: &DeterministicHashMap<Coefficient, Integer>,
    sign: Rational, // just one or negative one
    var_map: &mut DeterministicHashMap<u32, Var>,
    ctx: &mut ConvContext,
) -> (Vec<Mon<Rational>>, Rational) {
    // Each entry in expr is a (Coefficient, Integer) pair, but really the Integer part is what
    // should be the coefficient in the monomial we create. The "Coefficient" here either has a
    // term (by its id) or no term at all; i.e. 1.
    let mut monomials: Vec<Mon<Rational>> = Vec::new();
    let mut constant = Rational::ZERO;
    for (term_part, int_coeff) in expr {
        let rational_coeff = Rational::from(int_coeff.clone());
        match term_part {
            Coefficient::Term(id) => {
                let v = *var_map
                    .entry(*id)
                    .or_insert_with(|| ctx.allocate_var(&format!("!ext_var_{}", id), VarType::Int));
                monomials.push(Mon::new(&sign * &rational_coeff, v));
            }
            Coefficient::Constant => constant = -&sign * rational_coeff,
        }
    }
    (monomials, constant)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::incremental::{AssertOutcome, CheckResult};
    use crate::cnf::CNFConversion;
    use yaspar_ir::ast::{
        Context, GlobalSubst, LetElim, ObjectAllocatorExt, Repr, Term, TermAllocator, Typecheck,
        alg,
    };
    use yaspar_ir::untyped::UntypedAst;

    /// Build a `SolverState` from an `.smt2` string, mirroring the essential preprocessing
    /// pipeline in `main.rs` (parse → typecheck → collect asserts → nnf → insert_predecessor →
    /// cnf_tseitin). Enough to populate `arithmetic_terms` and the CNF `var_map`, which is all
    /// the static builder needs.
    fn setup_solver_state(smt: &str) -> SolverState {
        let commands = UntypedAst
            .parse_script_str(smt)
            .expect("parse failed");
        let mut context = Context::new();
        let typed = commands.type_check(&mut context).expect("typecheck failed");

        let mut assertions: Vec<Term> = typed
            .iter()
            .filter_map(|c| match c.repr() {
                alg::Command::Assert(t) => Some(t.clone()),
                _ => None,
            })
            .collect();

        let false_term = context.get_false();
        let not_false_term = context.not(false_term.clone());
        let true_term = context.get_true();
        assertions.push(true_term.clone());
        assertions.push(not_false_term);

        let mut solver_state = SolverState::new(context, false, false, false);
        solver_state.register_bool_constants(&true_term, &false_term);

        let global_names = solver_state.context.all_defined_symbols();
        for assert in assertions {
            let expanded = assert
                .let_elim(&mut solver_state.context)
                .gsubst(global_names.clone(), &mut solver_state.context);
            let nnf_term = expanded.nnf(&mut solver_state);
            solver_state.insert_predecessor(&nnf_term, None, None, false);
            let _ = nnf_term.cnf_tseitin(&mut solver_state);
        }
        solver_state
    }

    /// Collect every arithmetic atom literal (positive form) known to the CNF cache.
    fn arithmetic_atom_lits(solver_state: &mut SolverState) -> Vec<i32> {
        let mut uids: Vec<u64> = solver_state.cnf_cache.var_map.keys().copied().collect();
        uids.sort_unstable();
        let mut lits = vec![];
        for uid in uids {
            let lit = solver_state.get_lit_from_u64(uid);
            if extract_constraint_from_term(uid, true, solver_state).is_some() {
                lits.push(lit);
            }
        }
        lits
    }

    #[test]
    fn build_registers_both_polarities() {
        // Two atoms over one variable: (x <= 5) and (x >= 0), plus true/false.
        let smt = r#"
(declare-const x Int)
(assert (<= x 5))
(assert (>= x 0))
"#;
        let mut ss = setup_solver_state(smt);
        let atom_lits = arithmetic_atom_lits(&mut ss);
        assert!(!atom_lits.is_empty(), "expected arithmetic atoms");

        let solver = build_incremental_solver(&mut ss);
        // Each non-equality atom registers 2 polarities.
        for lit in &atom_lits {
            assert!(
                solver.atom_for_literal(*lit).is_some(),
                "positive literal {lit} should be registered"
            );
            assert!(
                solver.atom_for_literal(-*lit).is_some(),
                "negative literal {} should be registered",
                -*lit
            );
        }
    }

    /// Differential check: asserting a set of atom literals into the static solver and calling
    /// `check` must agree (sat vs unsat) with the one-shot `check_integer_constraints_satisfiable_lia`
    /// on the same literals.
    fn assert_agrees(smt: &str, lits_to_assert: &[i32]) {
        let mut ss = setup_solver_state(smt);

        // Incremental path.
        let mut solver = build_incremental_solver(&mut ss);
        let mut incremental_conflict = false;
        for &lit in lits_to_assert {
            if let Some(AssertOutcome::Conflict) = solver.assert_literal(lit) {
                incremental_conflict = true;
            }
        }
        let incremental_unsat =
            incremental_conflict || matches!(solver.check(), CheckResult::Unsat { .. });

        // One-shot path on the same literals. It negates literals internally, so pass them as-is.
        let one_shot = check_integer_constraints_satisfiable_lia(lits_to_assert, &mut ss);
        let one_shot_unsat = matches!(one_shot, ArithResult::Unsat(..));

        assert_eq!(
            incremental_unsat, one_shot_unsat,
            "incremental vs one-shot disagree on {smt:?} with lits {lits_to_assert:?}"
        );
    }

    #[test]
    fn differential_feasible() {
        let smt = r#"
(declare-const x Int)
(assert (<= x 5))
(assert (>= x 0))
"#;
        let mut ss = setup_solver_state(smt);
        let lits = arithmetic_atom_lits(&mut ss);
        // asserting both (x <= 5) and (x >= 0): feasible
        assert_agrees(smt, &lits);
    }

    #[test]
    fn differential_infeasible() {
        // x >= 5 and x <= 3 asserted together: infeasible.
        let smt = r#"
(declare-const x Int)
(assert (>= x 5))
(assert (<= x 3))
"#;
        let mut ss = setup_solver_state(smt);
        let lits = arithmetic_atom_lits(&mut ss);
        assert_agrees(smt, &lits);
    }

    #[test]
    fn differential_negated_polarity() {
        // Assert the *negation* of (x <= 3), i.e. x > 3, together with x <= 3's companion
        // bound x >= 5's negation etc. Here we drive the `-lit` (negated-constraint) path:
        // asserting ¬(x <= 3) [x > 3] and (x <= 2) is infeasible.
        let smt = r#"
(declare-const x Int)
(assert (<= x 3))
(assert (<= x 2))
"#;
        let mut ss = setup_solver_state(smt);
        let lits = arithmetic_atom_lits(&mut ss);
        // Negate the first atom literal (x <= 3 -> x > 3); keep x <= 2. x > 3 & x <= 2 is unsat.
        let mixed: Vec<i32> = vec![-lits[0], lits[1]];
        assert_agrees(smt, &mixed);
    }

    /// Stage 6 identity invariant: `var_for_term` returns a stable `Var` for each
    /// arithmetic term_id, independent of egraph merges performed after `build_incremental_solver`
    /// runs. The point isn't that the LP *knows about* the merge (Stage 7 wires that up);
    /// it's that the mapping between term_id and its arithmetic `Var` doesn't move under
    /// the caller's feet — a precondition for representing merges as bounds later.
    #[test]
    fn var_for_term_stable_across_egraph_merge() {
        // Two Int variables `x`, `y`, each with a comparison atom so both land in
        // `arithmetic_terms`.
        let smt = r#"
(declare-const x Int)
(declare-const y Int)
(assert (<= x 5))
(assert (<= y 3))
"#;
        let mut ss = setup_solver_state(smt);
        // Snapshot the arithmetic term list so we can pick two we know are distinct.
        let terms: Vec<u64> = ss.arithmetic_terms.clone();
        assert!(
            terms.len() >= 2,
            "expected at least two arithmetic terms, got {}",
            terms.len()
        );

        let solver = build_incremental_solver(&mut ss);

        // Pick the first two distinct arithmetic terms and confirm they map to
        // distinct `Var`s pre-merge.
        let t_a = terms[0];
        let t_b = terms[1];
        let v_a_pre = solver
            .var_for_term(t_a)
            .expect("var_for_term should be Some for arithmetic term");
        let v_b_pre = solver
            .var_for_term(t_b)
            .expect("var_for_term should be Some for arithmetic term");
        assert_ne!(
            v_a_pre, v_b_pre,
            "distinct terms should map to distinct Vars pre-merge"
        );

        // Merge the two terms in the egraph, at some arbitrary decision level.
        let e_a = ss.to_egraph_id(t_a);
        let e_b = ss.to_egraph_id(t_b);
        use crate::egraphs::EgraphTrait as _;
        let merge = ss.egraph.assert_equal(e_a, e_b, 1);
        assert!(
            merge.conflict.is_none(),
            "egraph assert_equal reported a conflict"
        );
        assert_eq!(
            ss.egraph.find(e_a),
            ss.egraph.find(e_b),
            "merge should have unified the two terms"
        );

        // Post-merge, the incremental solver's per-term mapping is unchanged.
        assert_eq!(solver.var_for_term(t_a), Some(v_a_pre));
        assert_eq!(solver.var_for_term(t_b), Some(v_b_pre));
        assert_ne!(
            solver.var_for_term(t_a),
            solver.var_for_term(t_b),
            "identity must survive merge — Stage 7 will convey the merge as a bound"
        );
    }

    /// Stage 6 regression: pre-Stage-6, `build_incremental_solver` skipped terms where
    /// `find(t) != t`. On a formula whose `arithmetic_terms` includes both a compound
    /// term `(x + y)` and its subterm `x`, the pristine pre-search egraph has each term
    /// as its own root, so the skip was inert — but the same code path had to survive
    /// dropping the skip without breaking the differential oracle. This test locks in
    /// that behaviour: multiple atoms sharing subterms still produce a solver whose
    /// verdict matches the one-shot path.
    #[test]
    fn differential_multi_term_sharing_subterms() {
        let smt = r#"
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x y) 5))
(assert (<= x 3))
"#;
        let mut ss = setup_solver_state(smt);
        let lits = arithmetic_atom_lits(&mut ss);
        assert_agrees(smt, &lits);

        // And a contradictory combination via a negated literal.
        let smt_bad = r#"
(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x y) 5))
(assert (>= x 10))
"#;
        let mut ss = setup_solver_state(smt_bad);
        let lits = arithmetic_atom_lits(&mut ss);
        assert_agrees(smt_bad, &lits);
    }
}
