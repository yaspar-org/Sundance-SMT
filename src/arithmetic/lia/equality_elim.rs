// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Equality elimination simplification pass for linear relations.
//!
//! Detects equalities of the form `x = c`, `x = y`, or `x = y + c` and substitutes
//! them throughout the system, eliminating variables before the simplex solver is invoked.

use dashu::Rational;
use std::collections::HashSet;

use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::linear_system::{Mon, Rel, combine_terms_helper};
use crate::arithmetic::lia::variables::Var;
use crate::debug_println;

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
    /// System became trivially UNSAT after elimination
    TriviallyUnsat(Var),
}

/// Attempt to extract a substitution from a normalized equality relation.
///
/// Pre-condition: `rel` is normalized (combined terms, integral, positive leading coeff).
fn detect_substitution(rel: &Rel<Rational>) -> Option<Substitution> {
    if !rel.is_equality() {
        return None;
    }

    let terms = rel.terms_ref();

    match terms.len() {
        // a*x = c  -->  x = c/a
        1 => {
            let var = terms[0].var();
            let coeff = terms[0].coeff_ref();
            let value = Rational::from(rel.constant_ref().clone()) / coeff;
            Some(Substitution::Constant { target: var, value })
        }
        // a*x + b*y = c
        // After normalization: leading coeff is positive and integral.
        // We match unit coefficients: +1*x + (-1)*y = c  means x = y + c
        2 => {
            let var_a = terms[0].var();
            let coeff_a = terms[0].coeff_ref();
            let var_b = terms[1].var();
            let coeff_b = terms[1].coeff_ref();

            // Check for unit coefficients +1 and -1
            if *coeff_a != Rational::ONE || *coeff_b != -Rational::ONE {
                return None;
            }

            // Normalized form: 1*x + (-1)*y = c, i.e., x - y = c, i.e., x = y + c
            // Eliminate the higher-ID variable
            let constant = rel.constant_ref().clone();

            if var_a.id > var_b.id {
                // target = var_a, replacement = var_b
                // var_a = var_b + c
                if constant.is_zero() {
                    Some(Substitution::Variable {
                        target: var_a,
                        replacement: var_b,
                    })
                } else {
                    Some(Substitution::Affine {
                        target: var_a,
                        replacement: var_b,
                        offset: constant,
                    })
                }
            } else {
                // target = var_b, replacement = var_a
                // From x - y = c: y = x - c
                if constant.is_zero() {
                    Some(Substitution::Variable {
                        target: var_b,
                        replacement: var_a,
                    })
                } else {
                    Some(Substitution::Affine {
                        target: var_b,
                        replacement: var_a,
                        offset: -constant,
                    })
                }
            }
        }
        _ => None,
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
pub fn equality_eliminate(ctx: &mut ConvContext) -> EqualityElimResult {
    for _iteration in 0..MAX_ITERATIONS {
        // Find a usable substitution
        let mut found_subst: Option<(usize, Substitution)> = None;
        for (idx, (rel, _var)) in ctx.get_relations().enumerate() {
            if let Some(subst) = detect_substitution(rel) {
                found_subst = Some((idx, subst));
                break;
            }
        }

        let (source_idx, subst) = match found_subst {
            Some(s) => s,
            None => break, // no more substitutions available
        };

        debug_println!(
            21,
            0,
            "lia::equality_elim: applying substitution {:?}",
            subst
        );

        // Apply the substitution to all other relations
        let mut to_remove = HashSet::new();
        let mut found_unsat: Option<Var> = None;

        for (rel, var) in ctx.get_relations_mut() {
            apply_substitution(rel, &subst);
            if rel.is_trivial_sat() {
                to_remove.insert(*var);
            } else if rel.is_trivial_unsat() {
                found_unsat = Some(*var);
                break;
            }
        }

        if let Some(conflict_var) = found_unsat {
            debug_println!(
                21,
                0,
                "lia::equality_elim: substitution produced UNSAT"
            );
            return EqualityElimResult::TriviallyUnsat(conflict_var);
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
            debug_println!(21, 0, "lia::equality_elim: system is trivially SAT");
            return EqualityElimResult::TriviallySat;
        }
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
        let subst = detect_substitution(&rel).unwrap();
        match subst {
            Substitution::Constant { target, value } => {
                assert_eq!(target, Var::real(0));
                assert_eq!(value, rbig!(3));
            }
            _ => panic!("expected Constant substitution"),
        }
    }

    #[test]
    fn test_detect_x_eq_y() {
        // x - y = 0 (normalized: leading coeff positive)
        let rel: Rel<Rational> = Rel::mk_eq(
            vec![Mon::new(rbig!(1), Var::real(0)), Mon::new(rbig!(-1), Var::real(1))],
            rbig!(0),
        );
        let subst = detect_substitution(&rel).unwrap();
        match subst {
            Substitution::Variable { target, replacement } => {
                assert_eq!(target, Var::real(1));
                assert_eq!(replacement, Var::real(0));
            }
            _ => panic!("expected Variable substitution"),
        }
    }

    #[test]
    fn test_detect_x_eq_y_plus_c() {
        // x - y = 5 (normalized)
        let rel: Rel<Rational> = Rel::mk_eq(
            vec![Mon::new(rbig!(1), Var::real(0)), Mon::new(rbig!(-1), Var::real(3))],
            rbig!(5),
        );
        let subst = detect_substitution(&rel).unwrap();
        match subst {
            Substitution::Affine {
                target,
                replacement,
                offset,
            } => {
                // var 3 > var 0, so target = var(3), replacement = var(0)
                // from x0 - x3 = 5: x3 = x0 - 5
                assert_eq!(target, Var::real(3));
                assert_eq!(replacement, Var::real(0));
                assert_eq!(offset, rbig!(-5));
            }
            _ => panic!("expected Affine substitution"),
        }
    }

    #[test]
    fn test_detect_non_unit_coefficients_returns_none() {
        // 2x - 3y = 5: coefficients are not unit, so no substitution
        let rel: Rel<Rational> = Rel::mk_eq(
            vec![Mon::new(rbig!(2), Var::real(0)), Mon::new(rbig!(-3), Var::real(1))],
            rbig!(5),
        );
        assert!(detect_substitution(&rel).is_none());
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
            vec![Mon::new(rbig!(1), Var::real(0)), Mon::new(rbig!(2), Var::real(1))],
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
        // Result: 5*x0 <= 10 (i.e., x0 <= 2)
        let subst = Substitution::Variable {
            target: Var::real(1),
            replacement: Var::real(0),
        };
        let mut rel: Rel<Rational> = Rel::mk_le(
            vec![Mon::new(rbig!(2), Var::real(0)), Mon::new(rbig!(3), Var::real(1))],
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
            vec![Mon::new(rbig!(1), Var::real(0)), Mon::new(rbig!(1), Var::real(1))],
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
        let _s1 = ctx.allocate_relation(Rel::mk_eq(
            vec![Mon::new(1, x), Mon::new(-1, y)],
            0,
        ));
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
        let _s1 = ctx.allocate_relation(Rel::mk_eq(
            vec![Mon::new(1, x), Mon::new(-1, y)],
            0,
        ));
        let _s2 = ctx.allocate_relation(Rel::mk_eq(
            vec![Mon::new(1, y), Mon::new(-1, z)],
            0,
        ));
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
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let _s1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x)], 3));
        let _s2 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x)], 5));

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        assert!(matches!(result, EqualityElimResult::TriviallyUnsat(_)));
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

        let _r1 =
            ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x34), Mon::new(-1, x13)], 0));
        let _r2 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x66)], 8));
        let _r3 = ctx.allocate_relation(Rel::mk_gt(vec![Mon::new(1, x59)], 0));

        preprocess(&mut ctx);
        let result = equality_eliminate(&mut ctx);

        assert!(matches!(result, EqualityElimResult::Unknown));
        // x34 = x13 and x66 = 8 should be eliminated, leaving only x59 > 0
        assert_eq!(ctx.num_relations(), 1);
        assert_eq!(ctx.get_substitutions().len(), 2);
    }
}
