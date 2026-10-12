// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::utils::FastDeterministicHashMap as HashMap;
use sat_interface::{Clause, Formula};
use yaspar_ir::ast::alg::CheckIdentifier;
use yaspar_ir::ast::{
    AConstant, ATerm, Context, FetchSort, IdentifierKind, ObjectAllocatorExt, Term, TermAllocator,
};
use yaspar_ir::traits::Repr;

/// Extended CNF conversion trait that provides our own implementations
/// while being compatible with yaspar-ir's CNFConversion trait
pub trait CNFConversion<Env> {
    /// Convert to CNF using Tseitin transformation (bidirectional encoding)
    fn cnf_tseitin(&self, env: &mut Env) -> Formula;

    /// Convert to Negative Normal Form (NNF)
    fn nnf(&self, env: &mut Env) -> Self;
}

/// Cache structure for CNF and NNF transformations
/// Reuses yaspar-ir's caching structure for compatibility
pub struct CNFCache {
    pub var_map: HashMap<u64, i32>,
    pub var_map_reverse: HashMap<i32, u64>,
    pub next_var: i32,
    pub nnf_cache: HashMap<u64, [Option<Term>; 2]>,
}

impl Default for CNFCache {
    fn default() -> Self {
        Self::new()
    }
}

impl CNFCache {
    pub(crate) fn new() -> Self {
        Self {
            var_map: HashMap::default(),
            var_map_reverse: HashMap::default(),
            next_var: 1,
            nnf_cache: HashMap::default(),
        }
    }
}

pub(crate) struct CNFEnv<'a> {
    pub(crate) context: &'a mut Context,
    pub(crate) cache: &'a mut CNFCache,
}

impl CNFEnv<'_> {
    fn new_var(&mut self) -> i32 {
        let v = self.cache.next_var;
        if v == i32::MAX {
            panic!("Too many boolean variables; reached i32::MAX!");
        }
        self.cache.next_var += 1;
        v
    }

    /// If the term has not yet received a literal in the `CNFCache`,
    /// allocates a fresh variable for it and stores it in the cache.
    /// The fresh variable is always positive, even if the term itself has a leading `Not`.
    ///
    /// Note: Only for use by the eDRAT proof system.
    /// Consider simplifying your terms with `nnf()` or `cnf_tseitin()` instead.
    pub fn new_var_for_term(&mut self, term: &Term) -> i32 {
        let uid = term.uid();
        if let Some(&lit) = self.cache.var_map.get(&uid) {
            lit
        } else {
            let v = self.new_var();
            self.cache.var_map.insert(uid, v);
            self.cache.var_map_reverse.insert(v, uid);
            v
        }
    }
}

/// Term-layer AC-completion for `and`/`or` (`SUNDANCE_AC=1`, off by default).
///
/// Canonicalizes a connective at the layer where terms, CNF literals and
/// trigger patterns are all born, so one AC-equivalence class is one `Term`,
/// one Tseitin literal and one e-graph node. This is what makes AC sound here:
/// the engine-level alternative (`register_set` on and/or) conflates distinct
/// driver terms that still carry distinct SAT literals, and the adapter's
/// conflict explainer then taints the run (99 regression files unsat -> unknown).
///
/// The canonical form is flatten + sort + dedup: nested same-op children are
/// spliced in (NNF builds bottom-up, so one layer here yields a fully flat
/// term), children are ordered by hash-cons id, and duplicates dropped
/// (idempotence). No constant is absorbed and a singleton is kept as is: the
/// transformation is exactly associativity + commutativity + idempotence.
///
/// Sorting by hash-cons id is safe only because trigger patterns never contain
/// a connective (measured: 0 of the regression files and 0 of 419 Verus files
/// have `and`/`or` inside a `:pattern`), so no pattern's child order has to
/// survive substitution. If that ever changes, `build_pattern_tree` must apply
/// the same canonicalization or the positional matcher misses.
fn ac_enabled() -> bool {
    static F: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *F.get_or_init(|| std::env::var("SUNDANCE_AC").is_ok_and(|v| v == "1"))
}

/// Diagnostic sub-switches, each on unless set to "0": SUNDANCE_AC_FLATTEN,
/// SUNDANCE_AC_SORT, SUNDANCE_AC_DEDUP. They exist to isolate which of the
/// three operations a regression or crash depends on; the shipped form is all
/// three.
fn ac_sub(name: &'static str) -> bool {
    std::env::var(name).map_or(true, |v| v != "0")
}

fn ac_canon(ts: Vec<Term>, is_and: bool) -> Vec<Term> {
    let mut acc: Vec<Term> = Vec::with_capacity(ts.len());
    let flatten = ac_sub("SUNDANCE_AC_FLATTEN");
    for t in ts {
        match t.repr() {
            ATerm::And(inner) if flatten && is_and => acc.extend(inner.iter().cloned()),
            ATerm::Or(inner) if flatten && !is_and => acc.extend(inner.iter().cloned()),
            _ => acc.push(t),
        }
    }
    if ac_sub("SUNDANCE_AC_SORT") {
        acc.sort_by_key(|t| t.uid());
    }
    if ac_sub("SUNDANCE_AC_DEDUP") {
        acc.dedup_by_key(|t| t.uid());
    }
    acc
}

fn ac_and(env: &mut CNFEnv, ts: Vec<Term>) -> Term {
    if !ac_enabled() {
        return env.context.and(ts);
    }
    let acc = ac_canon(ts, true);
    env.context.and(acc)
}

fn ac_or(env: &mut CNFEnv, ts: Vec<Term>) -> Term {
    if !ac_enabled() {
        return env.context.or(ts);
    }
    let acc = ac_canon(ts, false);
    env.context.or(acc)
}

/// Helper trait for internal CNF conversion implementations
trait CNFConversionHelper<Env> {
    fn nnf_impl(&self, env: &mut Env, polarity: bool) -> Self;
    fn cnf_nnf_tseitin(&self, env: &mut Env, formula: &mut Formula) -> i32;
}

impl CNFConversionHelper<CNFEnv<'_>> for Term {
    fn nnf_impl(&self, env: &mut CNFEnv, polarity: bool) -> Self {
        // Index in the cache array
        let idx = if polarity { 1 } else { 0 };

        // Cache lookup; return early if cache is hit
        if let Some(r) = &env
            .cache
            .nnf_cache
            .entry(self.uid())
            .or_insert_with(|| [None, None])[idx]
        {
            return r.clone();
        }

        let r = match self.repr() {
            ATerm::Annotated(t, _) => t.nnf_impl(env, polarity), // omit attributes
            ATerm::Eq(a, b) => {
                // Check if it's comparing two booleans
                let bs = env.context.bool_sort();
                let sa = a.get_sort(env.context);
                if sa != bs {
                    // If not, then we regard a = b as an atom
                    if polarity {
                        self.clone()
                    } else {
                        env.context.not(self.clone())
                    }
                } else {
                    // If so, then we convert a = b to a <=> b
                    let not_a = env.context.not(a.clone());
                    let not_b = env.context.not(b.clone());
                    // let a_i_b = env.context.flat_or(vec![not_a, b.clone()]);
                    // let b_i_a = env.context.flat_or(vec![not_b, a.clone()]);
                    // let eqf = env.context.flat_and(vec![a_i_b, b_i_a]);
                    let a_i_b = env.context.or(vec![not_a, b.clone()]);
                    let b_i_a = env.context.or(vec![not_b, a.clone()]);
                    let eqf = env.context.and(vec![a_i_b, b_i_a]);
                    eqf.nnf_impl(env, polarity)
                }
            }
            ATerm::Distinct(ts) => {
                let bs = env.context.bool_sort();
                let s = ts[0].get_sort(env.context);
                // Check if ts are booleans
                if bs != s {
                    // If not, then this term is considered atomic
                    if polarity {
                        self.clone()
                    } else {
                        env.context.not(self.clone())
                    }
                } else {
                    // Otherwise, we translate it into a boolean formula
                    match ts.len() {
                        // 1 => ts[0].sundance_nnf_impl(env, polarity),
                        2 => {
                            // If there are two terms, then these two must be unequal
                            let eq = env.context.eq(ts[0].clone(), ts[1].clone());
                            let eqf = env.context.not(eq);
                            eqf.nnf_impl(env, polarity)
                        }
                        _ => env.context.get_false().nnf_impl(env, polarity), // more than two distinct booleans are not possible
                    }
                }
            }
            ATerm::Constant(AConstant::Bool(b), _) => {
                if polarity {
                    self.clone()
                } else {
                    env.context.bool(!*b)
                }
            }
            ATerm::And(ts) => {
                match ts.len() {
                    0 => env.context.get_true().nnf_impl(env, polarity),
                    // 1 => ts[0].sundance_nnf_impl(env, polarity),
                    _ => {
                        let nts = ts
                            .iter()
                            .map(|t| t.nnf_impl(env, polarity))
                            .collect::<Vec<_>>();
                        if polarity {
                            // env.context.flat_and(nts)
                            ac_and(env, nts)
                        } else {
                            // notice that `(not (and a b))` is `(or (not a) (not b))`
                            ac_or(env, nts)
                        }
                    }
                }
            }
            ATerm::Or(ts) => {
                match ts.len() {
                    0 => env.context.get_false().nnf_impl(env, polarity),
                    // 1 => ts[0].sundance_nnf_impl(env, polarity),
                    _ => {
                        let nts = ts
                            .iter()
                            .map(|t| t.nnf_impl(env, polarity))
                            .collect::<Vec<_>>();
                        if polarity {
                            // env.context.flat_or(nts)
                            ac_or(env, nts)
                        } else {
                            // notice that `(not (or a b))` is `(and (not a) (not b))`
                            // env.context.flat_and(nts)
                            ac_and(env, nts)
                        }
                    }
                }
            }
            ATerm::Implies(ts, b) => {
                // notice `(=> a1 a2 ... an b)` is `(or (not a1) ... (not an) b)`
                let mut nts: Vec<_> = ts.iter().map(|t| t.nnf_impl(env, !polarity)).collect();
                let nb = b.nnf_impl(env, polarity);
                nts.push(nb);
                if polarity {
                    // env.context.flat_or(nts)
                    ac_or(env, nts)
                } else {
                    // env.context.flat_and(nts)
                    ac_and(env, nts)
                }
            }
            ATerm::Not(t) => t.nnf_impl(env, !polarity),
            ATerm::Ite(b, t, e) => {
                // notice `(ite b t e)` is `(or (and b t) (and (not b) e))`
                let not_b = env.context.not(b.clone());
                // let bt = env.context.flat_and(vec![b.clone(), t.clone()]);
                // let not_b_e = env.context.flat_and(vec![not_b, e.clone()]);
                // let eqf = env.context.flat_or(vec![bt, not_b_e]);
                let bt = env.context.and(vec![b.clone(), t.clone()]);
                let not_b_e = env.context.and(vec![not_b, e.clone()]);
                let eqf = env.context.or(vec![bt, not_b_e]);
                eqf.nnf_impl(env, polarity)
            }
            ATerm::Xor(ts) => {
                // `(xor a b)` is `(= (not a) b)`. Do a left-fold over the terms,
                // so that e.g. `(xor a1 a2 a3)` becomes `(= (not (= (not a1) a2)) a3)`
                let mut acc = ts[0].clone();
                for t in &ts[1..] {
                    let not_acc = env.context.not(acc.clone());
                    acc = env.context.eq(not_acc, t.clone());
                }
                acc.nnf_impl(env, polarity)
            }
            ATerm::App(f, args, _)
                if args.len() > 2
                    && matches!(
                        f.get_kind(),
                        Some(
                            IdentifierKind::Lt
                                | IdentifierKind::Le
                                | IdentifierKind::Gt
                                | IdentifierKind::Ge
                        )
                    ) =>
            {
                let bool_sort = env.context.bool_sort();
                let conjuncts = args
                    .windows(2)
                    .map(|c| {
                        env.context
                            .app(f.clone(), c.to_vec(), Some(bool_sort.clone()))
                    })
                    .collect();
                env.context.and(conjuncts).nnf_impl(env, polarity)
            }
            _ => {
                // all other cases are regarded as atoms
                if polarity {
                    self.clone()
                } else {
                    env.context.not(self.clone())
                }
            }
        };

        // Cache the result
        env.cache.nnf_cache.get_mut(&self.uid()).unwrap()[idx] = Some(r.clone());
        if polarity {
            // if polarity is positive, then we know nnf is idempotent
            let arr = env.cache.nnf_cache.entry(r.uid()).or_insert([None, None]);
            arr[1] = Some(r.clone());
        }
        r
    }

    /// Implements Tseitin transformation (bidirectional encoding)
    fn cnf_nnf_tseitin(&self, env: &mut CNFEnv, formula: &mut Formula) -> i32 {
        // Cache lookup
        if let Some(i) = env.cache.var_map.get(&self.uid()) {
            return *i;
        }

        let v = match self.repr() {
            ATerm::Constant(AConstant::Bool(b), _) => {
                let v = env.new_var();
                if !*b {
                    // the CNF of false is the negation of the false literal
                    formula.add(Clause::single(-v));
                }
                v
            }
            ATerm::And(ts) => match ts.len() {
                0 => env.context.get_true().cnf_nnf_tseitin(env, formula),
                // 1 => ts[0].sundance_cnf_nnf_tseitin(env, formula),
                _ => {
                    let nv = env.new_var();
                    let vs: Vec<_> = ts.iter().map(|t| t.cnf_nnf_tseitin(env, formula)).collect();
                    // Forward direction: x -> (a1 ∧ a2 ∧ ... ∧ an)
                    for v in vs.clone() {
                        formula.add(Clause::new(vec![v, -nv]))
                    }
                    // Backward direction: (a1 ∧ a2 ∧ ... ∧ an) -> x
                    let mut nvs: Vec<_> = vs.iter().map(|l| -l).collect();
                    nvs.push(nv);
                    formula.add(Clause::new(nvs));
                    nv
                }
            },
            ATerm::Or(ts) => match ts.len() {
                0 => env.context.get_false().cnf_nnf_tseitin(env, formula),
                // 1 => ts[0].sundance_cnf_nnf_tseitin(env, formula),
                _ => {
                    let nv = env.new_var();
                    let vs: Vec<_> = ts.iter().map(|t| t.cnf_nnf_tseitin(env, formula)).collect();
                    // Forward direction: x -> (a1 ∨ a2 ∨ ... ∨ an)
                    let mut forward_clause = vs.clone();
                    forward_clause.push(-nv);
                    formula.add(Clause::new(forward_clause));
                    // Backward direction: (a1 ∨ a2 ∨ ... ∨ an) -> x
                    for v in vs {
                        formula.add(Clause::new(vec![-v, nv]))
                    }
                    nv
                }
            },
            ATerm::Not(t) => -t.cnf_nnf_tseitin(env, formula),
            _ => env.new_var(),
        };

        env.cache.var_map.insert(self.uid(), v);
        env.cache.var_map_reverse.insert(v, self.uid());
        v
    }
}

impl CNFConversion<CNFEnv<'_>> for Term {
    fn cnf_tseitin(&self, env: &mut CNFEnv) -> Formula {
        // CNF conversion using Tseitin transformation
        let nnf = self.nnf(env);
        let mut formula = Formula::empty();
        let v = nnf.cnf_nnf_tseitin(env, &mut formula);
        formula.add(Clause::single(v));
        formula
    }

    fn nnf(&self, env: &mut CNFEnv) -> Self {
        self.nnf_impl(env, true)
    }
}

impl<Env> CNFConversion<Env> for Vec<Term>
where
    Term: CNFConversionHelper<Env>,
{
    fn cnf_tseitin(&self, env: &mut Env) -> Formula {
        let mut formula = Formula::empty();
        let nnfs = self.nnf(env);
        let lits = nnfs
            .iter()
            .map(|t| t.cnf_nnf_tseitin(env, &mut formula))
            .collect::<Vec<_>>();
        for l in lits {
            formula.add(Clause::single(l));
        }
        formula
    }

    fn nnf(&self, env: &mut Env) -> Self {
        self.iter()
            .flat_map(|t| {
                let t = t.nnf_impl(env, true);
                match t.repr() {
                    ATerm::And(ts) => ts.clone(),
                    _ => vec![t],
                }
            })
            .collect()
    }
}

/// Utility function to check if a term has no disjunctions
fn has_no_disjunction(t: &Term) -> bool {
    match t.repr() {
        ATerm::And(ts) => ts.iter().all(has_no_disjunction),
        ATerm::Or(_) => false,
        _ => true,
    }
}

/// Partition NNF terms into (those that have no disjunction, those that have disjunctions)
pub fn partition_nnfs(ts: Vec<Term>) -> (Vec<Term>, Vec<Term>) {
    ts.into_iter().partition(has_no_disjunction)
}

/// Inserts the literal, if valid, and returns `true` if the literal was inserted.
/// Otherwise, returns `false`.
///
/// The literal is not inserted if it is already in the clause
/// or if adding it would cause the clause to become a tautology.
pub fn push_literal(clause: &mut Vec<i32>, literal: i32) -> bool {
    assert!(literal != 0);
    if clause.contains(&-literal) || clause.contains(&literal) {
        false
    } else {
        clause.push(literal);
        true
    }
}

/// Inserts the literal only if it isn't already present in the clause
/// and if inserting it would not cause tautology.
///
/// Returns `true` if literal is in the clause after the function returns.
/// In other words, returns `true` if it was added or if it was already present.
pub fn push_literal_if_not_tautology(clause: &mut Vec<i32>, literal: i32) -> bool {
    assert!(literal != 0);
    if clause.contains(&-literal) {
        return false;
    } else if !clause.contains(&literal) {
        clause.push(literal);
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::Context;

    #[test]
    fn test_sundance_nnf_false() {
        let mut context = Context::default();
        let mut cache = CNFCache::new();
        let mut env = CNFEnv {
            context: &mut context,
            cache: &mut cache,
        };
        let terms = vec![env.context.get_false()];
        let nnf = terms.nnf(&mut env);
        assert_eq!(nnf, terms);
    }

    #[test]
    fn test_sundance_cnf_tseitin_conjunction() {
        let mut context = Context::default();
        let mut cache = CNFCache::new();
        let mut env = CNFEnv {
            context: &mut context,
            cache: &mut cache,
        };

        // Test: Simple conjunction (a ∧ b)
        let a = env.context.simple_symbol("a");
        let b = env.context.simple_symbol("b");
        let and_term = env.context.and(vec![a.clone(), b.clone()]);

        let formula = and_term.cnf_tseitin(&mut env);

        // Should have exactly 4 clauses for Tseitin transformation of (a ∧ b)
        assert_eq!(formula.0.len(), 4);

        // Verify variables exist in cache
        assert!(env.cache.var_map.contains_key(&a.uid()));
        assert!(env.cache.var_map.contains_key(&b.uid()));
        assert!(env.cache.var_map.contains_key(&and_term.uid()));
    }
}
