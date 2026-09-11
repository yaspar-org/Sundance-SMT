// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Up-front rejection of inputs Sundance cannot reason about.
//!
//! Any operator that `SolverState::extract_op` does not recognise is registered in the egraph as an
//! ordinary application (`Op::App`), so it is only constrained by congruence closure. For a theory
//! operator, that is unsound. Rather than answer incorrectly, we reject the input with an error
//! naming the theory and the offending term.
//!
//! The same applies to non-linear multiplication, which the arithmetic frontend cannot translate.
//! Rejecting it before the search rather than mid-solve matters: by the time
//! `extract_linear_expression` runs we are inside a CaDiCaL external-propagator callback, and cxx
//! turns any panic crossing that FFI boundary into `abort()`, a SIGABRT and a core dump instead of
//! an error message. Unlike the sort check, that one runs a little later (after let and `define-fun`
//! inlining) and is necessarily incomplete; see [`NonlinearityCheck`].

use crate::utils::{FastDeterministicHashMap, FastDeterministicHashSet};
use yaspar_ir::ast::alg::Constant;
use yaspar_ir::ast::{ATerm, Context, FetchSort, Repr, Term};
use yaspar_ir::statics::{ARRAY, BITVEC, REGLAN, SET, STRING};

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
    let mut seen = FastDeterministicHashSet::default();

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

/// Rejects *ground* non-linear multiplication, one term at a time.
///
/// [`Self::check`] rejects any `*` with two or more factors that do not fold to a constant. That is
/// precisely the condition under which `extract_linear_expression` panics.
///
/// **A product mentioning a bound variable is exempt**, even when it looks non-linear. The Verus
/// prelude asserts `(forall ((x Int) (y Int)) (! (= (Mul x y) (* x y)) :pattern ((Mul x y))))`, and
/// `(* x y)` is never handed to the arithmetic frontend as written, only its instantiations
/// are. Rejecting on the body would reject essentially every Verus input.
///
/// The cost of that exemption is that this check is *not* complete: an instantiation can still
/// produce a genuinely non-linear ground product at solve time, and that still reaches the `panic!`
/// in `extract_linear_expression`.
///
/// Because of the exemption, the check has to run on the assertions the arithmetic frontend will
/// actually see, i.e. *after* let-elimination and global substitution — inlining a `let` or a
/// `define-fun` can turn an exempt product into a ground non-linear one, as in
/// `(let ((y x)) (* x y))`. `main` therefore drives it per assertion inside the preprocessing loop.
/// Sharing one instance across those calls also shares the memo tables below.
///
/// Terms are hash-consed, so a subterm reached along several paths is the same allocation. Keying
/// the tables on `Term::uid` keeps the whole check linear in the number of distinct subterms, rather
/// than quadratic in the nesting depth of products.
#[derive(Default)]
pub struct NonlinearityCheck {
    /// Terms whose subtree [`Self::check`] has already walked.
    walked: FastDeterministicHashSet<u64>,
    /// Memoized [`Self::folds_to_constant`].
    folds: FastDeterministicHashMap<u64, bool>,
    /// Memoized [`Self::contains_bound_variable`].
    bound: FastDeterministicHashMap<u64, bool>,
}

impl NonlinearityCheck {
    /// Does `term` fold to a numeric constant, in exactly the sense
    /// `extract_linear_expression` folds one?
    ///
    /// Deliberately narrow, and kept in step with the `ATerm::Constant` and `App` arms of
    /// `extract_linear_expression` (`arithmetic/lp.rs`):
    ///
    /// * only `Constant::Numeral` counts -- a `Decimal` makes that function panic rather than fold
    /// * only `+`, `-` and `*` fold. `div` and `mod` become `Coefficient::Div`/`Mod` keys and `abs`
    ///   and `/` fall through to the uninterpreted arm, so all four behave like variables even when
    ///   applied to numerals
    /// * everything else (variables, `ite`, uninterpreted applications, annotated terms) becomes its
    ///   own variable
    fn folds_to_constant(&mut self, term: &Term) -> bool {
        if let Some(&cached) = self.folds.get(&term.uid()) {
            return cached;
        }
        let folds = match term.repr() {
            ATerm::Constant(c, _) => matches!(c, Constant::Numeral(_)),
            ATerm::App(identifier, args, _) => {
                matches!(identifier.0.symbol.as_str(), "+" | "-" | "*")
                    && args.iter().all(|arg| self.folds_to_constant(arg))
            }
            _ => false,
        };
        self.folds.insert(term.uid(), folds);
        folds
    }

    /// Does `term` mention a variable bound by an enclosing quantifier, `let`, or `match` arm?
    ///
    /// Such a term is not what the arithmetic frontend will eventually see: quantifier
    /// instantiation substitutes for the bound variable first, and the result is often linear even
    /// when the body is not. See [`NonlinearityCheck`] for why that forces us to defer.
    fn contains_bound_variable(&mut self, term: &Term) -> bool {
        if let Some(&cached) = self.bound.get(&term.uid()) {
            return cached;
        }
        let bound = matches!(term.repr(), ATerm::Local(_))
            || term
                .repr()
                .sub_terms()
                .any(|sub| self.contains_bound_variable(sub));
        self.bound.insert(term.uid(), bound);
        bound
    }

    /// Reject `assertion` if it contains a ground non-linear multiplication.
    pub fn check(&mut self, assertion: &Term) -> Result<(), String> {
        let mut stack: Vec<&Term> = vec![assertion];

        while let Some(term) = stack.pop() {
            if !self.walked.insert(term.uid()) {
                continue;
            }

            if let ATerm::App(identifier, args, _) = term.repr()
                && identifier.0.symbol.as_str() == "*"
                && args.iter().filter(|a| !self.folds_to_constant(a)).count() >= 2
                && !self.contains_bound_variable(term)
            {
                return Err(format!(
                    "non-linear multiplication is not supported: `{term}`."
                ));
            }

            stack.extend(term.repr().sub_terms());
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::{GlobalSubst, LetElim, Typecheck, alg};
    use yaspar_ir::untyped::UntypedAst;

    /// Parse and typecheck `input`, returning its assertions along with the context.
    fn assertions_of(input: &str) -> (Vec<Term>, Context) {
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
        (assertions, context)
    }

    /// Parse and typecheck `input`, then run the theory check over its assertions.
    fn check(input: &str) -> Result<(), String> {
        let (assertions, mut context) = assertions_of(input);
        reject_unsupported_theories(&assertions, &mut context)
    }

    /// Parse and typecheck `input`, then run the non-linearity check over its raw assertions.
    fn check_linear(input: &str) -> Result<(), String> {
        let (assertions, _context) = assertions_of(input);
        let mut check = NonlinearityCheck::default();
        assertions.iter().try_for_each(|a| check.check(a))
    }

    /// Like [`check_linear`], but eliminating lets and inlining global definitions first, as `main`
    /// does. Only this order catches products that inlining creates.
    fn check_linear_expanded(input: &str) -> Result<(), String> {
        let (assertions, mut context) = assertions_of(input);
        let mut check = NonlinearityCheck::default();
        for assertion in &assertions {
            let expanded = assertion.let_elim(&mut context).gsubst_all(&mut context);
            check.check(&expanded)?;
        }
        Ok(())
    }

    /// Wrap `term` in a minimal script declaring `x`, `y`, `z` so the cases below stay readable.
    fn with_int_vars(term: &str) -> String {
        format!(
            "(declare-const x Int)\n(declare-const y Int)\n(declare-const z Int)\n\
             (assert (= {term} 0))\n(check-sat)\n"
        )
    }

    #[test]
    fn accepts_linear_products() {
        // Each of these has at most one non-constant factor once constants are folded.
        for term in [
            "x",
            "(* 2 x)",
            "(* x 2)",
            "(* 2 3 x)",
            "(* x (* 2 3))",
            "(* (- 3 5) x)",
            "(* (+ x 1) 2)",
            "(* (* x 2) 3)",
            "(* 0 x)",
        ] {
            let result = check_linear(&with_int_vars(term));
            assert!(result.is_ok(), "unexpected rejection of {term}: {result:?}");
        }
    }

    #[test]
    fn rejects_nonlinear_products() {
        for term in [
            "(* x y)",
            "(* x x)",
            "(* 2 x y)",
            "(* x y z)",
            "(* (+ x 1) y)",
            "(* (* x 2) y)",
            // div/mod never fold, so they act as variables here.
            "(* (div 6 2) x)",
        ] {
            let result = check_linear(&with_int_vars(term));
            let msg = result.expect_err(&format!("{term} should be rejected"));
            assert!(msg.contains("non-linear multiplication"), "{msg}");
        }
    }

    /// A non-linear product nested inside an otherwise linear one is still caught, since the walk
    /// visits every subterm.
    #[test]
    fn rejects_nonlinear_product_nested_under_linear_one() {
        let result = check_linear(&with_int_vars("(* 2 (* x y))"));
        assert!(
            result.is_err(),
            "nested non-linear product should be rejected"
        );
    }

    /// A ground non-linear product is caught even when it sits inside a binder's scope, as long as
    /// it does not itself mention the bound variable.
    #[test]
    fn rejects_ground_nonlinear_product_inside_binder_scope() {
        let under_let = check_linear(
            r#"
(declare-const x Int)
(assert (let ((y (* x x))) (= y 4)))
(check-sat)
"#,
        );
        assert!(
            under_let.is_err(),
            "ground non-linear product under let should be rejected"
        );

        let under_forall = check_linear(
            r#"
(declare-const x Int)
(declare-const y Int)
(assert (forall ((z Int)) (> (* x y) z)))
(check-sat)
"#,
        );
        assert!(
            under_forall.is_err(),
            "ground non-linear product under forall should be rejected"
        );
    }

    /// A product over quantified variables is deferred, not rejected: instantiation substitutes for
    /// the bound variables first, and the result is usually linear. This is the Verus prelude's
    /// `prelude_mul` axiom, present in every Verus-generated file — rejecting it would reject the
    /// whole corpus.
    #[test]
    fn accepts_nonlinear_product_over_bound_variables() {
        let prelude_mul = r#"
(declare-fun Mul (Int Int) Int)
(assert (forall ((x Int) (y Int)) (! (= (Mul x y) (* x y)) :pattern ((Mul x y)))))
(check-sat)
"#;
        let result = check_linear(prelude_mul);
        assert!(result.is_ok(), "unexpected rejection: {result:?}");
        // Let-elimination does not touch a quantifier body, so the axiom is still accepted at the
        // point `main` actually checks it.
        let expanded = check_linear_expanded(prelude_mul);
        assert!(expanded.is_ok(), "unexpected rejection: {expanded:?}");
    }

    /// Only one factor needs to be bound for the product to be deferred.
    #[test]
    fn accepts_product_mixing_bound_and_free_variables() {
        let result = check_linear(
            r#"
(declare-const x Int)
(assert (forall ((y Int)) (= (* x y) 0)))
(check-sat)
"#,
        );
        assert!(result.is_ok(), "unexpected rejection: {result:?}");
    }

    /// Inlining a `let` can turn a product that mentions a bound variable — and so is exempt as
    /// written — into a ground non-linear one. Checking after let-elimination catches it.
    #[test]
    fn rejects_nonlinear_product_created_by_let_inlining() {
        let input = r#"
(declare-const x Int)
(assert (let ((y x)) (= (* x y) 0)))
(check-sat)
"#;
        assert!(
            check_linear(input).is_ok(),
            "`(* x y)` mentions a bound variable, so it is exempt before inlining"
        );
        let msg =
            check_linear_expanded(input).expect_err("should be rejected after let-elimination");
        assert!(msg.contains("non-linear multiplication"), "{msg}");
    }

    /// Likewise for a `define-fun` body: the product is not in any assertion until global
    /// substitution inlines it.
    #[test]
    fn rejects_nonlinear_product_created_by_define_fun_inlining() {
        let input = r#"
(declare-const x Int)
(define-fun square ((a Int)) Int (* a a))
(assert (= (square x) 4))
(check-sat)
"#;
        assert!(
            check_linear(input).is_ok(),
            "the product lives in the definition, not the assertion, before inlining"
        );
        let msg =
            check_linear_expanded(input).expect_err("should be rejected after global substitution");
        assert!(msg.contains("non-linear multiplication"), "{msg}");
    }

    #[test]
    fn accepts_arithmetic_without_multiplication() {
        let result = check_linear(
            r#"
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (= (f x) (+ x 1)))
(assert (> (div x 2) (mod x 3)))
(check-sat)
"#,
        );
        assert!(result.is_ok(), "unexpected rejection: {result:?}");
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
