// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Equality elimination simplification pass for linear relations.
//!
//! Detects equalities of the form `x = c`, `x = y`, or `x = y + c` and substitutes
//! them throughout the system, eliminating variables before the simplex solver is invoked.

use dashu::Rational;
use std::collections::{BTreeSet, HashMap, HashSet};

use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::linear_system::{Mon, Rel, combine_terms_helper};
use crate::arithmetic::lia::solver_result::Conflict;
use crate::arithmetic::lia::variables::{Var, VarType};
use crate::debug_println;

// Maximum number of eliminations to perform
const MAX_ITERATIONS: usize = 255;

/// A substitution extracted from an equality relation
#[derive(Debug, Clone)]
pub enum Substitution {
    /// x = c (single-variable equality solved for a constant)
    Constant {
        /// Variable being eliminated
        target: Var,
        /// Constant value to substitute
        value: Rational,
    },
    /// x = y (target has higher ID, eliminated in favor of replacement)
    Variable {
        /// Variable being eliminated
        target: Var,
        /// Variable replacing it
        replacement: Var,
    },
    /// x = y + c (target has higher ID, eliminated in favor of replacement + offset)
    Affine {
        /// Variable being eliminated
        target: Var,
        /// Variable replacing it
        replacement: Var,
        /// Constant offset added to replacement
        offset: Rational,
    },
}

/// Result of equality elimination
#[derive(Debug)]
pub enum EqualityElimResult {
    /// System has been simplified; satisfiability is unknown
    Unknown,
    /// System became trivially SAT after elimination
    TriviallySat,
    /// System became trivially UNSAT after elimination; conflict includes all contributing
    /// relations
    TriviallyUnsat(Conflict<Var>),
}

/// Result of attempting to detect a substitution from an equality
enum DetectResult {
    /// A valid substitution was found
    Found(Substitution),
    /// The equality is trivially unsatisfiable (e.g., 2*x = 1 with Int x); eliminating
    /// x in this case can be unsound
    Unsat,
    /// No substitution could be extracted
    None,
}

/// Attempt to extract a substitution from a normalized equality relation.
///
/// Pre-condition: `rel` is normalized (combined terms, integral, positive leading coeff).
///
/// The pre-condition is satisfied if the [`crate::arithmetic::lia::preprocess`]ing pass is
/// performed directly before equality elimination.
fn detect_substitution(rel: &Rel<Rational>) -> DetectResult {
    if !rel.is_equality() {
        return DetectResult::None;
    }

    let terms = rel.terms_ref();

    match terms.len() {
        // a*x = c  -->  x = c/a
        1 => {
            let var = terms[0].var();
            let coeff = terms[0].coeff_ref();
            let value = Rational::from(rel.constant_ref().clone()) / coeff;
            if var.typ == VarType::Int && !value.is_int() {
                return DetectResult::Unsat;
            }
            DetectResult::Found(Substitution::Constant { target: var, value })
        }
        // a*x + b*y = c
        // After normalization: leading coeff is positive and integral.
        // We match unit coefficients: +1*x + (-1)*y = c  means x = y + c
        //
        // TODO: lia::equality_elim::detect_substitution: support non-unit two-term substitutions
        2 => {
            let var_a = terms[0].var();
            let coeff_a = terms[0].coeff_ref();
            let var_b = terms[1].var();
            let coeff_b = terms[1].coeff_ref();

            // Check for unit coefficients +1 and -1
            if *coeff_a != Rational::ONE || *coeff_b != -Rational::ONE {
                return DetectResult::None;
            }

            // Normalized form: 1*x + (-1)*y = c, i.e., x - y = c, i.e., x = y + c
            // Eliminate the higher-ID variable
            let constant = rel.constant_ref().clone();

            if var_a.id > var_b.id {
                // target = var_a, replacement = var_b
                // var_a = var_b + c
                if constant.is_zero() {
                    DetectResult::Found(Substitution::Variable {
                        target: var_a,
                        replacement: var_b,
                    })
                } else {
                    DetectResult::Found(Substitution::Affine {
                        target: var_a,
                        replacement: var_b,
                        offset: constant,
                    })
                }
            } else {
                // target = var_b, replacement = var_a
                // From x - y = c: y = x - c
                if constant.is_zero() {
                    DetectResult::Found(Substitution::Variable {
                        target: var_b,
                        replacement: var_a,
                    })
                } else {
                    DetectResult::Found(Substitution::Affine {
                        target: var_b,
                        replacement: var_a,
                        offset: -constant,
                    })
                }
            }
        }
        _ => DetectResult::None,
    }
}

/// Apply a substitution to a single relation, modifying it in place.
///
/// After application, the relation is re-normalized.
fn apply_substitution(rel: &mut Rel<Rational>, subst: &Substitution) {
    let target = match subst {
        Substitution::Constant { target, .. }
        | Substitution::Variable { target, .. }
        | Substitution::Affine { target, .. } => *target,
    };

    // Check if the target variable appears in this relation
    if !rel.terms_ref().iter().any(|m| m.var() == target) {
        return;
    }

    match subst {
        Substitution::Constant { value, .. } => {
            // For each term a_i * target: remove term, subtract a_i * value from the
            // constant side. Recall: terms = constant, so subtracting from constant
            // means the new constant = old_constant - a_i * value.
            let mut new_terms = Vec::new();
            let mut constant_adjustment = Rational::ZERO;
            for mon in rel.terms_ref() {
                if mon.var() == target {
                    constant_adjustment += mon.coeff_ref() * value;
                } else {
                    new_terms.push(Mon::new(mon.coeff_ref().clone(), mon.var()));
                }
            }
            rel.set_terms(new_terms);
            *rel.constant_mut() -= &constant_adjustment;
        }
        Substitution::Variable { replacement, .. } => {
            // Replace target with replacement in terms
            let new_terms: Vec<Mon<Rational>> = rel
                .terms_ref()
                .iter()
                .map(|mon| {
                    if mon.var() == target {
                        // a * target => a * replacement
                        Mon::new(mon.coeff_ref().clone(), *replacement)
                    } else {
                        Mon::new(mon.coeff_ref().clone(), mon.var())
                    }
                })
                .collect();
            rel.set_terms(new_terms);
        }
        Substitution::Affine {
            replacement,
            offset,
            ..
        } => {
            // target = replacement + offset
            // For a_i * target: becomes a_i * replacement, and constant -= a_i * offset
            let mut new_terms = Vec::new();
            let mut constant_adjustment = Rational::ZERO;
            for mon in rel.terms_ref() {
                if mon.var() == target {
                    new_terms.push(Mon::new(mon.coeff_ref().clone(), *replacement));
                    constant_adjustment += mon.coeff_ref() * offset;
                } else {
                    new_terms.push(Mon::new(mon.coeff_ref().clone(), mon.var()));
                }
            }
            rel.set_terms(new_terms);
            *rel.constant_mut() -= &constant_adjustment;
        }
    }

    // After substitution, combine duplicate variables and re-normalize
    let combined = combine_terms_helper(rel.terms_ref());
    rel.set_terms(combined);
    rel.normalize();
}

/// Run equality elimination on a ConvContext.
///
/// Pre-condition: all relations have been normalized (i.e., `preprocess` has run).
/// Post-condition: all extractable simple equalities have been substituted away.
/// Provenance is stored in `ctx` for later conflict expansion.
pub fn equality_eliminate(ctx: &mut ConvContext) -> EqualityElimResult {
    // Local provenance tracker; will be flushed into ctx at the end or on early return.
    let mut provenance: HashMap<Var, BTreeSet<Var>> = HashMap::new();

    for _iteration in 0..MAX_ITERATIONS {
        // Find a usable substitution and its source relation's slack var
        let mut found_subst: Option<(usize, Var, Substitution)> = None;
        for (idx, (rel, var)) in ctx.get_relations().enumerate() {
            match detect_substitution(rel) {
                DetectResult::Found(subst) => {
                    found_subst = Some((idx, *var, subst));
                    break;
                }
                DetectResult::Unsat => {
                    debug_println!(21, 0, "lia::equality_elim: integrality conflict detected");
                    let mut conflict_set = BTreeSet::new();
                    conflict_set.insert(*var);
                    if let Some(prov) = provenance.get(var) {
                        conflict_set.extend(prov.iter().copied());
                    }
                    return EqualityElimResult::TriviallyUnsat(Conflict::from_set(conflict_set));
                }
                DetectResult::None => {}
            }
        }

        let (source_idx, src_var, subst) = match found_subst {
            Some(s) => s,
            None => break, // no more substitutions available
        };

        debug_println!(
            21,
            0,
            "lia::equality_elim: applying substitution {:?}",
            subst
        );

        // Compute the full provenance of the source equality (itself + its own provenance)
        let mut src_provenance = BTreeSet::new();
        src_provenance.insert(src_var);
        if let Some(existing) = provenance.get(&src_var) {
            src_provenance.extend(existing.iter().copied());
        }

        // Apply the substitution to all other relations
        let mut to_remove = HashSet::new();
        let mut found_unsat: Option<Var> = None;

        for (rel, var) in ctx.get_relations_mut() {
            let var_copy = *var;
            apply_substitution(rel, &subst);
            if rel.is_trivial_sat() {
                to_remove.insert(var_copy);
            } else if rel.is_trivial_unsat() {
                found_unsat = Some(var_copy);
                break;
            }
        }

        // Update provenance for all relations (the source equality's provenance
        // is inherited by every relation it was substituted into)
        for (_rel, var) in ctx.get_relations() {
            let var_copy = *var;
            if var_copy != src_var {
                provenance
                    .entry(var_copy)
                    .or_default()
                    .extend(src_provenance.iter().copied());
            }
        }

        if let Some(conflict_var) = found_unsat {
            debug_println!(21, 0, "lia::equality_elim: substitution produced UNSAT");
            // Build conflict: the contradicted relation + all equalities folded into it
            let mut conflict_set = BTreeSet::new();
            conflict_set.insert(conflict_var);
            if let Some(prov) = provenance.get(&conflict_var) {
                conflict_set.extend(prov.iter().copied());
            }
            return EqualityElimResult::TriviallyUnsat(Conflict::from_set(conflict_set));
        }

        // Also mark the source equality for removal (it becomes 0 = 0 after self-substitution)
        if let Some((_rel, var)) = ctx.get_relations().nth(source_idx) {
            to_remove.insert(*var);
        }

        // Remove trivially-sat relations and the source equality
        ctx.filter_vars(|v| !to_remove.contains(v));

        // Record the substitution for model back-substitution
        ctx.record_substitution(subst);

        if ctx.num_relations() == 0 {
            debug_println!(
                21,
                0,
                "lia::equality_elim: empty system after equality elimination: system is trivially SAT"
            );
            return EqualityElimResult::TriviallySat;
        }
    }

    // Store provenance in the context for later conflict expansion by the solver
    for (var, sources) in &provenance {
        ctx.add_provenance(*var, sources);
    }

    EqualityElimResult::Unknown
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::arithmetic::lia::context::ConvContext;
    use crate::arithmetic::lia::linear_system::{Mon, Rel};
    use crate::arithmetic::lia::preprocess::preprocess;
    use crate::arithmetic::lia::types::rbig;
    use crate::arithmetic::lia::variables::{Var, VarType};

    #[test]
    fn test_detect_x_eq_const() {
        // 2x = 6  (normalized)
        let rel: Rel<Rational> = Rel::mk_eq(vec![Mon::new(rbig!(2), Var::real(0))], rbig!(6));
        match detect_substitution(&rel) {
            DetectResult::Found(Substitution::Constant { target, value }) => {
                assert_eq!(target, Var::real(0));
                assert_eq!(value, rbig!(3));
            }
            _ => panic!("expected Found(Constant) substitution"),
        }
    }

    #[test]
    fn test_detect_x_eq_y() {
        // x - y = 0 (normalized: leading coeff positive)
        let rel: Rel<Rational> = Rel::mk_eq(
            vec![
                Mon::new(rbig!(1), Var::real(0)),
                Mon::new(rbig!(-1), Var::real(1)),
            ],
            rbig!(0),
        );
        match detect_substitution(&rel) {
            DetectResult::Found(Substitution::Variable {
                target,
                replacement,
            }) => {
                assert_eq!(target, Var::real(1));
                assert_eq!(replacement, Var::real(0));
            }
            _ => panic!("expected Found(Variable) substitution"),
        }
    }

    #[test]
    fn test_detect_x_eq_y_plus_c() {
        // x - y = 5 (normalized)
        let rel: Rel<Rational> = Rel::mk_eq(
            vec![
                Mon::new(rbig!(1), Var::real(0)),
                Mon::new(rbig!(-1), Var::real(3)),
            ],
            rbig!(5),
        );
        match detect_substitution(&rel) {
            DetectResult::Found(Substitution::Affine {
                target,
                replacement,
                offset,
            }) => {
                // var(3) > var(0), so target = var(3), replacement = var(0)
                // from x0 - x3 = 5: x3 = x0 - 5
                assert_eq!(target, Var::real(3));
                assert_eq!(replacement, Var::real(0));
                assert_eq!(offset, rbig!(-5));
            }
            _ => panic!("expected Found(Affine) substitution"),
        }
    }

    #[test]
    fn test_detect_non_unit_coefficients_returns_none() {
        // 2x - 3y = 5: coefficients are not unit, so no substitution
        let rel: Rel<Rational> = Rel::mk_eq(
            vec![
                Mon::new(rbig!(2), Var::real(0)),
                Mon::new(rbig!(-3), Var::real(1)),
            ],
            rbig!(5),
        );
        assert!(matches!(detect_substitution(&rel), DetectResult::None));
    }

    // regression test from original equality elimination impl bug
    #[test]
    fn test_detect_int_non_integral_returns_unsat() {
        // 2x = 1 with Int x: x = 1/2 is not integral, so UNSAT
        let rel: Rel<Rational> = Rel::mk_eq(vec![Mon::new(rbig!(2), Var::int(0))], rbig!(1));
        assert!(matches!(detect_substitution(&rel), DetectResult::Unsat));
    }

    #[test]
    fn test_apply_constant_substitution() {
        // Substitution: x0 = 3
        // Relation: x0 + 2*x1 <= 10
        // Result: 2*x1 <= 7
        let subst = Substitution::Constant {
            target: Var::real(0),
            value: rbig!(3),
        };
        let mut rel: Rel<Rational> = Rel::mk_le(
            vec![
                Mon::new(rbig!(1), Var::real(0)),
                Mon::new(rbig!(2), Var::real(1)),
            ],
            rbig!(10),
        );
        apply_substitution(&mut rel, &subst);

        let expected = Rel::mk_le(vec![Mon::new(rbig!(2), Var::real(1))], rbig!(7));
        assert!(rel.equivalent(&expected));
    }

    #[test]
    fn test_apply_variable_substitution() {
        // Substitution: x1 = x0
        // Relation: 2*x0 + 3*x1 <= 10
        // Result: 5*x0 <= 10 (after normalization, x0 <= 2)
        let subst = Substitution::Variable {
            target: Var::real(1),
            replacement: Var::real(0),
        };
        let mut rel: Rel<Rational> = Rel::mk_le(
            vec![
                Mon::new(rbig!(2), Var::real(0)),
                Mon::new(rbig!(3), Var::real(1)),
            ],
            rbig!(10),
        );
        apply_substitution(&mut rel, &subst);

        let expected = Rel::mk_le(vec![Mon::new(rbig!(1), Var::real(0))], rbig!(2));
        assert!(rel.equivalent(&expected));
    }

    #[test]
    fn test_apply_affine_substitution() {
        // Substitution: x1 = x0 + 2
        // Relation: x0 + x1 <= 10
        // Result: x0 + (x0 + 2) <= 10  -->  2*x0 <= 8  -->  x0 <= 4
        let subst = Substitution::Affine {
            target: Var::real(1),
            replacement: Var::real(0),
            offset: rbig!(2),
        };
        let mut rel: Rel<Rational> = Rel::mk_le(
            vec![
                Mon::new(rbig!(1), Var::real(0)),
                Mon::new(rbig!(1), Var::real(1)),
            ],
            rbig!(10),
        );
        apply_substitution(&mut rel, &subst);

        let expected = Rel::mk_le(vec![Mon::new(rbig!(1), Var::real(0))], rbig!(4));
        assert!(rel.equivalent(&expected));
    }

    #[test]
    fn test_equality_eliminate_x_eq_const() {
        // System: x = 3, x + y <= 10
        // After elimination: y <= 7
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let _s1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x)], 3));
        let _s2 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x), Mon::new(1, y)], 10));

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        assert!(matches!(result, EqualityElimResult::Unknown));
        assert_eq!(ctx.num_relations(), 1);
        // remaining relation should be y <= 7
        let (rel, _) = ctx.get_relations().next().unwrap();
        let expected = Rel::mk_le(vec![Mon::new(rbig!(1), y)], rbig!(7));
        assert!(rel.equivalent(&expected));
    }

    #[test]
    fn test_equality_eliminate_x_eq_y() {
        // System: x = y, x + y <= 10
        // After elimination: 2y <= 10 (i.e., y <= 5)
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let _s1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x), Mon::new(-1, y)], 0));
        let _s2 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x), Mon::new(1, y)], 10));

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        assert!(matches!(result, EqualityElimResult::Unknown));
        assert_eq!(ctx.num_relations(), 1);
        let (rel, _) = ctx.get_relations().next().unwrap();
        let expected = Rel::mk_le(vec![Mon::new(rbig!(1), x)], rbig!(5));
        assert!(rel.equivalent(&expected));
    }

    #[test]
    fn test_equality_eliminate_transitive_chain() {
        // System: x = y, y = z, z >= 1
        // After elimination: x >= 1
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let z = ctx.allocate_var("z", VarType::Real);
        let _s1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x), Mon::new(-1, y)], 0));
        let _s2 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, y), Mon::new(-1, z)], 0));
        let _s3 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, z)], 1));

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        assert!(matches!(result, EqualityElimResult::Unknown));
        assert_eq!(ctx.num_relations(), 1);
        let (rel, _) = ctx.get_relations().next().unwrap();
        let expected = Rel::mk_ge(vec![Mon::new(rbig!(1), x)], rbig!(1));
        assert!(rel.equivalent(&expected));
    }

    #[test]
    fn test_equality_eliminate_produces_unsat() {
        // System: x = 3, x >= 5
        // After substitution: 0 >= 2 which is trivially unsat
        // Conflict must include both the equality and the inequality
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let s1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x)], 3));
        let s2 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x)], 5));

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        match result {
            EqualityElimResult::TriviallyUnsat(conflict) => {
                assert!(
                    conflict.contains(&s1),
                    "conflict must include the source equality"
                );
                assert!(
                    conflict.contains(&s2),
                    "conflict must include the contradicted relation"
                );
                assert_eq!(conflict.len(), 2);
            }
            _ => panic!("expected TriviallyUnsat"),
        }
    }

    #[test]
    fn test_equality_eliminate_trivially_sat() {
        // System: x = 3, x <= 5
        // After substitution: 0 <= 2 which is trivially sat, and the source equality
        // is also removed, leaving no relations.
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let _s1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x)], 3));
        let _s2 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x)], 5));

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        assert!(matches!(result, EqualityElimResult::TriviallySat));
    }

    #[test]
    fn test_carpark_style_elimination() {
        // Simplified version of the Carpark benchmark pattern:
        // x34 = x13, x66 = 8, x59 > 0
        let mut ctx = ConvContext::new();
        let x13 = ctx.allocate_var("x13", VarType::Real);
        let x34 = ctx.allocate_var("x34", VarType::Real);
        let x59 = ctx.allocate_var("x59", VarType::Real);
        let x66 = ctx.allocate_var("x66", VarType::Real);

        let _r1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x34), Mon::new(-1, x13)], 0));
        let _r2 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x66)], 8));
        let _r3 = ctx.allocate_relation(Rel::mk_gt(vec![Mon::new(1, x59)], 0));

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        assert!(matches!(result, EqualityElimResult::Unknown));
        // x34 = x13 and x66 = 8 should be eliminated, leaving only x59 > 0
        assert_eq!(ctx.num_relations(), 1);
        assert_eq!(ctx.get_substitutions().len(), 2);
    }

    /// Regression test based on equality_elim_conflict_regression.smt2
    ///
    /// v_3 + 1 = 5 (i.e., v_3 = 4) and v_3 < 4 conflict.
    /// The conflict must include both the source equality and the contradicted inequality.
    #[test]
    fn test_equality_elim_conflict_includes_source_equality() {
        let mut ctx = ConvContext::new();
        let v3 = ctx.allocate_var("v3", VarType::Int);
        let s1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, v3)], 4)); // v3 = 4
        let s2 = ctx.allocate_relation(Rel::mk_lt(vec![Mon::new(1, v3)], 4)); // v3 < 4

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        match result {
            EqualityElimResult::TriviallyUnsat(conflict) => {
                assert!(
                    conflict.contains(&s1),
                    "conflict must include the source equality"
                );
                assert!(
                    conflict.contains(&s2),
                    "conflict must include the contradicted relation"
                );
                assert_eq!(conflict.len(), 2);
            }
            _ => panic!("expected TriviallyUnsat"),
        }
    }

    /// Regression test for transitive equality chains producing conflicts.
    ///
    /// x = y, y = 5, x > 5  →  after elimination: 5 > 5 (unsat)
    /// Conflict must include all three relations.
    #[test]
    fn test_equality_elim_conflict_transitive_chain() {
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let s1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x), Mon::new(-1, y)], 0)); // x = y
        let s2 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, y)], 5)); // y = 5
        let s3 = ctx.allocate_relation(Rel::mk_gt(vec![Mon::new(1, x)], 5)); // x > 5

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        match result {
            EqualityElimResult::TriviallyUnsat(conflict) => {
                assert!(conflict.contains(&s1), "conflict must include x = y");
                assert!(conflict.contains(&s2), "conflict must include y = 5");
                assert!(conflict.contains(&s3), "conflict must include x > 5");
                assert_eq!(conflict.len(), 3);
            }
            _ => panic!("expected TriviallyUnsat"),
        }
    }
}
