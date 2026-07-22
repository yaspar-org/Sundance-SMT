// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Skolemization of existential quantifiers

use crate::debug_println;
use yaspar_ir::ast::ATerm::{Annotated, Exists, Forall};
use yaspar_ir::ast::alg::QualifiedIdentifier;
use yaspar_ir::ast::subst::{Substitute, Substitution};
use yaspar_ir::ast::{Context, FreshVar, Repr, Sort, Str, Term, TermAllocator};

/// skolemize quantified terms with a given polarity
///
/// it uses skolem variables to transform the original term into an equivalent one.
///
/// returns the transformed term and an association of skolem variables and sorts
pub fn skolemize(term: &Term, context: &mut Context, polarity: bool) -> (Term, Vec<(Str, Sort)>) {
    match term.repr() {
        Forall(var_bindings, body) => {
            if polarity {
                panic_not_quant(term);
            } else {
                // Create a fresh skolem variable for each existentially quantified variable
                debug_println!(6, 0, "We are skolemizing the term {}", term);
                let mut skolem_substitutions = Substitution::empty();

                let mut skolem_variables = vec![];

                for var_binding in var_bindings {
                    let skolem_symbol = context.fresh_var("skolem-variable");
                    debug_println!(
                        26,
                        0,
                        "(declare-const {} {})",
                        skolem_symbol,
                        var_binding.2.clone()
                    );

                    skolem_variables.push((skolem_symbol.clone(), var_binding.2.clone()));
                    let skolem_id = QualifiedIdentifier::simple(skolem_symbol);
                    let skolem_term = context.global(skolem_id, Some(var_binding.2.clone()));

                    // Key the substitution on the bound variable's `Local` (id + symbol + sort)
                    // so distinct variables that print identically never collide.
                    skolem_substitutions.push(var_binding.clone().into(), skolem_term);
                }

                let deannotated_body = if let Annotated(inner_term, _) = body.repr() {
                    inner_term
                } else {
                    // if no annotation, assuming we have the body
                    body
                };
                // Substitute the skolem variables into the body
                let substituted_term = deannotated_body.subst(&skolem_substitutions, context);

                let negated_substituted_term = context.not(substituted_term);
                (negated_substituted_term, skolem_variables)
            }
        }
        Exists(var_bindings, body) => {
            // For existential quantifiers, we create fresh skolem variables
            // The skolem variables should depend on any universally quantified variables
            // that are in scope, but for simplicity, we'll create simple skolem variables

            // Create a fresh skolem variable for each existentially quantified variable
            if !polarity {
                panic_not_quant(term);
            } else {
                // Create a fresh skolem variable for each existentially quantified variable
                debug_println!(6, 0, "We are skolemizing the term {}", term);
                let mut skolem_substitutions = Substitution::empty();

                let mut skolem_variables = vec![];

                for var_binding in var_bindings {
                    let skolem_symbol = context.fresh_var("skolem-variable");
                    debug_println!(
                        26,
                        0,
                        "(declare-const {} {})",
                        skolem_symbol,
                        var_binding.2.clone()
                    );

                    skolem_variables.push((skolem_symbol.clone(), var_binding.2.clone()));
                    let skolem_id = QualifiedIdentifier::simple(skolem_symbol);
                    let skolem_term = context.global(skolem_id, Some(var_binding.2.clone()));

                    // Key the substitution on the bound variable's `Local` (id + symbol + sort)
                    // so distinct variables that print identically never collide.
                    skolem_substitutions.push(var_binding.clone().into(), skolem_term);
                }

                let deannotated_body = if let Annotated(inner_term, _) = body.repr() {
                    inner_term
                } else {
                    // if no annotation, assuming we have the body
                    body
                };
                // Substitute the skolem variables into the body
                let substituted_term = deannotated_body.subst(&skolem_substitutions, context);

                (substituted_term, skolem_variables)
            }
        }
        _ => panic_not_quant(term),
    }
}

/// Calls `panic!()` with a message that `term` is not a quantifier.
fn panic_not_quant(term: &Term) -> ! {
    panic!(
        "We can only skolemize an existential or a negated forall, not {}",
        term
    );
}
