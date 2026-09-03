// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Up-front rejection of inputs that use theories Sundance cannot reason about.
//!
//! Any operator that `SolverState::extract_op` does not recognise is registered in the egraph as an
//! ordinary application (`Op::App`), so it is only constrained by congruence closure. For a theory
//! operator, that is unsound. Rather than answer incorrectly, we reject the input with an error
//! naming the theory and the offending term.

use yaspar_ir::ast::{Context, FetchSort, Repr, Term};
use yaspar_ir::statics::{BITVEC, STRING, ARRAY, REGLAN, SET};

/// The theory name for a sort Sundance has no decision procedure for, or `None` if the sort is
/// supported.
fn unsupported_theory(sort_name: &str) -> Option<&'static str> {
    match sort_name {
        BITVEC => Some("fixed-size bitvectors"),
        STRING => Some("strings"),
        REGLAN => Some("regular expressions"),
        ARRAY => Some("arrays"),
        SET => Some("sets"),
        _ => None,
    }
}

/// Reject `assertions` if any subterm belongs to an unsupported theory.
///
/// Detection is by sort rather than by operator.
///
/// Call this as early as possible: it wants the raw typechecked assertions, before let-elimination,
/// NNF, or any egraph registration, so detecting an unsupported input costs little beyond parsing.
/// `sub_terms` descends into let bindings and quantifier bodies, so nothing has to be expanded
/// first for the walk to be complete.
pub fn reject_unsupported_theories(
    assertions: &[Term],
    context: &mut Context,
) -> Result<(), String> {
    let mut stack: Vec<&Term> = assertions.iter().collect();
    // Terms are hash-consed, so subterms are shared within and across assertions. Memoizing on
    // uid keeps the walk linear in the number of distinct subterms.
    let mut seen = crate::utils::FastDeterministicHashSet::default();

    while let Some(term) = stack.pop() {
        if !seen.insert(term.uid()) {
            continue;
        }

        let sort = term.get_sort(context);
        if let Some(theory) = unsupported_theory(sort.sort_name().as_str()) {
            return Err(format!(
                "unsupported theory: {theory}. The term `{term}` has sort `{sort}`, \
                 and Sundance has no decision procedure for this theory."
            ));
        }

        stack.extend(term.repr().sub_terms());
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::{Typecheck, alg};
    use yaspar_ir::untyped::UntypedAst;

    /// Parse and typecheck `input`, then run the theory check over its assertions.
    fn check(input: &str) -> Result<(), String> {
        let commands = UntypedAst.parse_script_str(input).expect("parse failed");
        let mut context = Context::new();
        let typed = commands.type_check(&mut context).expect("typecheck failed");
        let assertions: Vec<Term> = typed
            .iter()
            .filter_map(|c| match c.repr() {
                alg::Command::Assert(t) => Some(t.clone()),
                _ => None,
            })
            .collect();
        reject_unsupported_theories(&assertions, &mut context)
    }

    #[test]
    fn accepts_uf_and_arithmetic() {
        let result = check(
            r#"
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (= (f x) (+ x 1)))
(check-sat)
"#,
        );
        assert!(result.is_ok(), "unexpected rejection: {result:?}");
    }

    #[test]
    fn rejects_bitvector_operator() {
        let result = check(
            r#"
(declare-const x (_ BitVec 8))
(assert (= (bvor x #b00000000) x))
(check-sat)
"#,
        );
        let msg = result.expect_err("bitvector input should be rejected");
        assert!(msg.contains("fixed-size bitvectors"), "{msg}");
        assert!(msg.contains("BitVec"), "{msg}");
    }

    /// `bvult` returns Bool, so the rejection has to come from its arguments.
    #[test]
    fn rejects_bitvector_predicate() {
        let result = check(
            r#"
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvult x y))
(check-sat)
"#,
        );
        assert!(result.is_err(), "bitvector predicate should be rejected");
    }

    /// Bitvectors reachable only through a let binding are still caught.
    #[test]
    fn rejects_bitvector_under_let() {
        let result = check(
            r#"
(declare-const x (_ BitVec 4))
(assert (let ((y (bvnot x))) (= y x)))
(check-sat)
"#,
        );
        assert!(result.is_err(), "bitvector under let should be rejected");
    }

    /// A declared bitvector constant that no assertion mentions is harmless.
    #[test]
    fn accepts_unused_bitvector_declaration() {
        let result = check(
            r#"
(declare-const unused (_ BitVec 8))
(declare-const b Bool)
(assert (or b (not b)))
(check-sat)
"#,
        );
        assert!(result.is_ok(), "unexpected rejection: {result:?}");
    }
}
