use sat_interface::{Clause, Formula};
use std::collections::HashMap;
use yaspar_ir::ast::{
    AConstant, ATerm, Context, FetchSort, ObjectAllocatorExt, Term, TermAllocator,
};
use yaspar_ir::traits::Repr;

/// Extended CNF conversion trait that provides our own implementations
/// while being compatible with yaspar-ir's CNFConversion trait
pub trait CNFConversion<Env> {
    /// Convert to CNF using Tseitin transformation (bidirectional encoding)
    fn cnf_tseitin(&self, env: Env) -> Formula;

    /// Convert to Negative Normal Form (NNF)
    fn nnf(&self, env: Env) -> Self;

    /// Convert to CNF using Plaisted-Greenbaum transformation
    fn cnf(&self, env: Env) -> Formula;
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
    pub fn new() -> Self {
        Self {
            var_map: HashMap::new(),
            var_map_reverse: HashMap::new(),
            next_var: 1,
            nnf_cache: HashMap::new(),
        }
    }
}

pub struct SundanceCNFEnv {
    pub context: Context,
    pub cache: CNFCache,
}

impl SundanceCNFEnv {
    fn new_var(&mut self) -> i32 {
        let v = self.cache.next_var;
        if v == i32::MAX {
            panic!("Too many boolean variables; reached i32::MAX!");
        }
        self.cache.next_var += 1;
        v
    }
}

/// Helper trait for internal CNF conversion implementations
trait CNFConversionHelper<Env> {
    fn nnf_impl(&self, env: Env, polarity: bool) -> Self;
    fn cnf_nnf(&self, env: Env, formula: &mut Formula) -> i32;
    fn cnf_nnf_tseitin(&self, env: Env, formula: &mut Formula) -> i32;
}

impl CNFConversionHelper<&mut SundanceCNFEnv> for Term {
    fn nnf_impl(&self, env: &mut SundanceCNFEnv, polarity: bool) -> Self {
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
                let sa = a.get_sort(&mut env.context);
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
                let s = ts[0].get_sort(&mut env.context);
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
                            .map(|t| t.nnf_impl(&mut *env, polarity))
                            .collect::<Vec<_>>();
                        if polarity {
                            // env.context.flat_and(nts)
                            env.context.and(nts)
                        } else {
                            // notice that `(not (and a b))` is `(or (not a) (not b))`
                            env.context.or(nts)
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
                            .map(|t| t.nnf_impl(&mut *env, polarity))
                            .collect::<Vec<_>>();
                        if polarity {
                            // env.context.flat_or(nts)
                            env.context.or(nts)
                        } else {
                            // notice that `(not (or a b))` is `(and (not a) (not b))`
                            // env.context.flat_and(nts)
                            env.context.and(nts)
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
                    env.context.or(nts)
                } else {
                    // env.context.flat_and(nts)
                    env.context.and(nts)
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

    /// Implements Plaisted-Greenbaum (PG) transformation
    fn cnf_nnf(&self, env: &mut SundanceCNFEnv, formula: &mut Formula) -> i32 {
        // Cache lookup
        if let Some(i) = env.cache.var_map.get(&self.uid()) {
            return *i;
        }

        let v = match self.repr() {
            ATerm::Constant(AConstant::Bool(b), _) => {
                let v = env.new_var();
                if *b {
                    // the CNF of true is just a fresh variable
                    v
                } else {
                    formula.add(Clause::single(-v));
                    v
                }
            }
            ATerm::And(ts) => match ts.len() {
                0 => env.context.get_true().cnf_nnf(env, formula),
                // 1 => ts[0].sundance_cnf_nnf(env, formula),
                _ => {
                    let nv = env.new_var();
                    let vs: Vec<_> = ts.iter().map(|t| t.cnf_nnf(env, formula)).collect();
                    for v in vs {
                        formula.add(Clause::new(vec![v, -nv]))
                    }
                    nv
                }
            },
            ATerm::Or(ts) => match ts.len() {
                0 => env.context.get_false().cnf_nnf(env, formula),
                // 1 => ts[0].sundance_cnf_nnf(env, formula),
                _ => {
                    let nv = env.new_var();
                    let mut vs: Vec<_> = ts.iter().map(|t| t.cnf_nnf(env, formula)).collect();
                    vs.push(-nv);
                    formula.add(Clause::new(vs));
                    nv
                }
            },
            ATerm::Not(t) => -t.cnf_nnf(env, formula),
            _ => env.new_var(),
        };

        env.cache.var_map.insert(self.uid(), v);
        env.cache.var_map_reverse.insert(v, self.uid());
        v
    }

    /// Implements Tseitin transformation (bidirectional encoding)
    fn cnf_nnf_tseitin(&self, env: &mut SundanceCNFEnv, formula: &mut Formula) -> i32 {
        // Cache lookup
        if let Some(i) = env.cache.var_map.get(&self.uid()) {
            return *i;
        }

        let v = match self.repr() {
            ATerm::Constant(AConstant::Bool(b), _) => {
                let v = env.new_var();
                if *b {
                    // the CNF of true is just a fresh variable
                    v
                } else {
                    formula.add(Clause::single(-v));
                    v
                }
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

impl CNFConversion<&mut SundanceCNFEnv> for Term {
    fn cnf_tseitin(&self, env: &mut SundanceCNFEnv) -> Formula {
        // CNF conversion using Tseitin transformation
        let nnf = self.nnf(&mut *env);
        let mut formula = Formula::empty();
        let v = nnf.cnf_nnf_tseitin(env, &mut formula);
        formula.add(Clause::single(v));
        formula
    }

    fn nnf(&self, env: &mut SundanceCNFEnv) -> Self {
        self.nnf_impl(env, true)
    }

    fn cnf(&self, env: &mut SundanceCNFEnv) -> Formula {
        // CNF conversion using Plaisted-Greenbaum transformation
        let nnf = self.nnf(&mut *env);
        let mut formula = Formula::empty();
        let v = nnf.cnf_nnf(env, &mut formula);
        formula.add(Clause::single(v));
        formula
    }
}

impl CNFConversion<&mut SundanceCNFEnv> for Vec<Term> {
    fn cnf_tseitin(&self, env: &mut SundanceCNFEnv) -> Formula {
        let mut formula = Formula::empty();
        let nnfs = self.nnf(&mut *env);
        let lits = nnfs
            .iter()
            .map(|t| t.cnf_nnf_tseitin(env, &mut formula))
            .collect::<Vec<_>>();
        for l in lits {
            formula.add(Clause::single(l));
        }
        formula
    }

    fn nnf(&self, env: &mut SundanceCNFEnv) -> Self {
        self.iter()
            .flat_map(|t| {
                let t = t.nnf(&mut *env);
                match t.repr() {
                    ATerm::And(ts) => ts.clone(),
                    _ => vec![t],
                }
            })
            .collect()
    }

    fn cnf(&self, env: &mut SundanceCNFEnv) -> Formula {
        let mut formula = Formula::empty();
        let nnfs = self.nnf(&mut *env);
        let lits = nnfs
            .iter()
            .map(|t| t.cnf_nnf(env, &mut formula))
            .collect::<Vec<_>>();
        for l in lits {
            formula.add(Clause::single(l));
        }
        formula
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

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::Context;

    #[test]
    fn test_sundance_nnf_false() {
        let context = Context::default();
        let cache = CNFCache::new();
        let mut env = SundanceCNFEnv { context, cache };
        let terms = vec![env.context.get_false()];
        let nnf = terms.nnf(&mut env);
        assert_eq!(nnf, terms);
    }

    #[test]
    fn test_sundance_cnf_tseitin_conjunction() {
        let context = Context::default();
        let cache = CNFCache::new();
        let mut env = SundanceCNFEnv { context, cache };

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
