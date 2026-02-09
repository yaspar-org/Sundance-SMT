// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Defines an intermediate representation in between the `frontend.rs` and the [LRASolver] simplex
//! solver.
//!
//! [Mon] (linear monomials), [Rel] (linear relations), and [LinearSystem] (sets of linear
//! relations) are the main types. From a [LinearSystem], one can create a a simplex solver and
//! determine satisfiability over the rationals, integers, or a mixture.

use dashu::base::{Abs, Gcd};
use dashu::{Integer, Rational};
// Note: num_traits feature in dashu must be enabled for the Integer/Rational impl of Zero to be
// in scope.
use num_traits::Zero;
use std::collections::{HashMap, HashSet};
use std::error;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::ops;

use crate::arithmetic::lia::bounds::Bounds;
use crate::arithmetic::lia::context::ConvContext;
use crate::arithmetic::lia::lra_solver::LRASolver;
use crate::arithmetic::lia::qdelta::QDelta;
use crate::arithmetic::lia::tableau_dense::TableauDense;
use crate::arithmetic::lia::utils;
use crate::arithmetic::lia::variables::{Owner, Var, VarInfo};

/// Generic frontend error
#[derive(Debug)]
pub struct LinearSystemError(String);

type LinearSystemResult<T> = Result<T, LinearSystemError>;

impl fmt::Display for LinearSystemError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "FrontendError: {}", self.0)
    }
}
impl error::Error for LinearSystemError {}

/// Represent a linear monomial term: a * x, a is rational, x is a variable
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Mon<T> {
    var: Var,
    coeff: T,
}

/// Ordering for MonTerm ignores the coefficient
impl<T: PartialEq> PartialOrd for Mon<T> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.var.cmp(&other.var))
    }
}

impl<T: Eq> Ord for Mon<T> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.partial_cmp(other).unwrap()
    }
}

impl<T: Hash> Hash for Mon<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.var.hash(state);
        self.coeff.hash(state);
    }
}

impl<T> Mon<T> {
    /// Create a new monomial term with the given coefficient and variable.
    pub fn new(coeff: impl Into<T>, var: Var) -> Self {
        Mon {
            coeff: coeff.into(),
            var,
        }
    }
}

impl<T: Zero + Ord> Mon<T> {
    /// is coefficient zero
    pub fn coeff_zero(&self) -> bool {
        self.coeff.is_zero()
    }

    /// is coefficient strictly positive
    pub fn coeff_pos(&self) -> bool {
        self.coeff > T::zero()
    }

    /// is coefficient strictly negative
    ///
    /// Currently only used in tests.
    #[allow(dead_code)]
    pub fn coeff_neg(&self) -> bool {
        self.coeff < T::zero()
    }
}

impl<T: ops::Neg<Output = T>> ops::Neg for Mon<T> {
    type Output = Self;

    fn neg(self) -> Self {
        Mon {
            coeff: -self.coeff,
            ..self
        }
    }
}

impl<T: for<'a> ops::Mul<&'a Rational, Output = T>> ops::Mul<&Rational> for Mon<T> {
    type Output = Self;

    fn mul(self, rhs: &Rational) -> Self {
        Mon {
            coeff: self.coeff * rhs,
            ..self
        }
    }
}

impl<T: for<'a> ops::Div<&'a Rational, Output = T>> ops::Div<&Rational> for Mon<T> {
    type Output = Self;

    fn div(self, rhs: &Rational) -> Self {
        Mon {
            coeff: self.coeff / rhs,
            ..self
        }
    }
}

/// Represents an addend in a linear expression - either a scalar times a variable or a constant
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Addend<T> {
    /// A scalar times a variable (coefficient * variable)
    Term(Mon<T>),
    /// A constant value
    Constant(T),
}

impl<T> Addend<T> {
    /// Create a term addend from a coefficient and variable
    pub fn term(coeff: impl Into<T>, var: Var) -> Self {
        Addend::Term(Mon::new(coeff, var))
    }

    /// Create a constant addend
    ///
    /// Currently only used in tests.
    #[allow(dead_code)]
    pub fn constant(value: impl Into<T>) -> Self {
        Addend::Constant(value.into())
    }

    /// Helper function to separate addends into terms and constants
    ///
    /// TODO: return an interator over terms?
    pub fn separate_addends(addends: &[Addend<T>]) -> (Vec<Mon<T>>, T)
    where
        T: Clone + Zero + for<'a> ops::Add<&'a T, Output = T>,
    {
        let mut terms = Vec::new();
        let mut constant_sum = T::zero();

        for addend in addends {
            match addend {
                Addend::Term(mon) => terms.push((*mon).clone()),
                Addend::Constant(c) => {
                    constant_sum = constant_sum + c;
                }
            }
        }

        (terms, constant_sum)
    }
}

impl<T: ops::Neg<Output = T>> ops::Neg for Addend<T> {
    type Output = Self;

    fn neg(self) -> Self {
        match self {
            Addend::Term(m) => Addend::Term(-m),
            Addend::Constant(c) => Addend::Constant(-c),
        }
    }
}

impl<T: for<'a> ops::Mul<&'a Rational, Output = T>> ops::Mul<&Rational> for Addend<T> {
    type Output = Self;

    fn mul(self, rhs: &Rational) -> Self {
        match self {
            Addend::Term(m) => Addend::Term(m * rhs),
            Addend::Constant(c) => Addend::Constant(c * rhs),
        }
    }
}

impl<T: for<'a> ops::Div<&'a Rational, Output = T>> ops::Div<&Rational> for Addend<T> {
    type Output = Self;

    fn div(self, rhs: &Rational) -> Self {
        match self {
            Addend::Term(m) => Addend::Term(m / rhs),
            Addend::Constant(c) => Addend::Constant(c / rhs),
        }
    }
}

/// Type of arithmetic relation
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Constraint {
    /// equality
    Eq,
    /// less than or equal
    Le,
    /// strictly less
    Lt,
    /// greater than or equal
    Ge,
    /// strictly greater
    Gt,
}

impl Constraint {
    /// Reverse the constraint type as you would when multiplying the relation by -1.
    pub fn reverse(&self) -> Self {
        match self {
            Constraint::Eq => Constraint::Eq,
            Constraint::Le => Constraint::Ge,
            Constraint::Lt => Constraint::Gt,
            Constraint::Ge => Constraint::Le,
            Constraint::Gt => Constraint::Lt,
        }
    }

    /// Negate the constraint type; corresponds to negating a relation
    pub fn negate(&self) -> Option<Self> {
        match self {
            // TODO: pre-processing of equality negation into (r > b) or (r < b) is not implemented
            Constraint::Eq => None,
            Constraint::Le => Some(Constraint::Gt),
            Constraint::Lt => Some(Constraint::Ge),
            Constraint::Ge => Some(Constraint::Lt),
            Constraint::Gt => Some(Constraint::Le),
        }
    }

    /// Test whether `Rational::ZERO <constraint> val` holds, where <constraint> represents
    /// `self`
    fn test_zero(&self, val: &Rational) -> bool {
        match self {
            Constraint::Eq => val.is_zero(),
            Constraint::Le => Rational::ZERO <= *val,
            Constraint::Lt => Rational::ZERO < *val,
            Constraint::Ge => Rational::ZERO >= *val,
            Constraint::Gt => Rational::ZERO > *val,
        }
    }
}

/// Represent an (in)equality with homogeneous terms on one side; think
/// "terms are constraint_type than constant".
///
/// - Le case: sum_{i=1}^n a_i x_i <= b, where a_i, b are rational and x_i denote rational variables.
/// - Ge case: b <= sum_{i=1}^n a_i x_i
/// - Eq case: sum_{i=1}^n a_i x_i = b
///
/// Homogeneous terms are allowed to represent rational multiples of the same variable and have
/// coefficient zero. Note that these relations may be trivially true or false if all coefficients
/// are zero.
#[derive(Debug, Clone)]
pub struct Rel<T> {
    constraint_type: Constraint,
    terms: Vec<Mon<T>>,
    constant: T,
}

/// Important: equality on `Rel` is structural, not mathematical.
impl<T: PartialEq> PartialEq for Rel<T> {
    fn eq(&self, other: &Self) -> bool {
        self.constraint_type == other.constraint_type
            && self.terms == other.terms
            && self.constant == other.constant
    }
}

impl<T> Eq for Rel<T> where T: Eq {}

impl<T> Hash for Rel<T>
where
    T: Hash,
{
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.constraint_type.hash(state);
        self.terms.hash(state);
        self.constant.hash(state);
    }
}

impl<T> Rel<T> {
    /// Verbose constructor for relations
    pub fn mk(constraint_type: Constraint, terms: Vec<Mon<T>>, constant: impl Into<T>) -> Self {
        Self {
            constraint_type,
            terms,
            constant: constant.into(),
        }
    }

    /// Make an equality relation: terms = constant
    pub fn mk_eq(terms: Vec<Mon<T>>, constant: impl Into<T>) -> Self {
        Self::mk(Constraint::Eq, terms, constant.into())
    }

    /// Make an less or equal relation: terms <= constant
    pub fn mk_le(terms: Vec<Mon<T>>, constant: impl Into<T>) -> Self {
        Self::mk(Constraint::Le, terms, constant.into())
    }

    /// Make an strictly less than relation: terms < constant
    pub fn mk_lt(terms: Vec<Mon<T>>, constant: impl Into<T>) -> Self {
        Self::mk(Constraint::Lt, terms, constant.into())
    }

    /// Make an greater or equal relation: terms >= constant
    pub fn mk_ge(terms: Vec<Mon<T>>, constant: impl Into<T>) -> Self {
        Self::mk(Constraint::Ge, terms, constant.into())
    }

    /// Make an strictly greater than relation: terms > constant
    pub fn mk_gt(terms: Vec<Mon<T>>, constant: impl Into<T>) -> Self {
        Self::mk(Constraint::Gt, terms, constant.into())
    }

    /// Create a relation (terms <rel> constant) from a left-hand side list of addends, a relation type,
    /// and a right-hand side.
    ///
    /// For example: x0 - 3x1 + 4 <= 2 x0 - 5 --> -1 x0 - 2 x0 - 3 x1 <= -9
    ///
    /// Note: the left hand side of the resulting relation is not necessarily combined using [combine_terms].
    pub fn from_addends_lhs_rhs(
        lhs: Vec<Addend<T>>,
        rel_type: Constraint,
        rhs: Vec<Addend<T>>,
    ) -> Self
    where
        // TODO: a lot of this is over-generalization given that we only care about Rational through the front end
        T: Clone
            + Zero
            + for<'a> ops::Add<&'a T, Output = T>
            + ops::Neg<Output = T>
            + ops::Sub<Output = T>,
    {
        // Convert LHS rel_type RHS to (LHS - RHS) rel_type 0 by
        // separating LHS and RHS into terms and constants and combining.
        let (lhs_terms, lhs_constant) = Addend::separate_addends(&lhs);
        let (rhs_terms, rhs_constant) = Addend::separate_addends(&rhs);

        // Combine terms: lhs_terms - rhs_terms
        let mut combined_terms = Vec::with_capacity(lhs_terms.len() + rhs_terms.len());
        combined_terms.extend(lhs_terms);
        for rhs_term in rhs_terms {
            combined_terms.push(-rhs_term);
        }
        let combined_constant = rhs_constant - lhs_constant;
        Self::mk(rel_type, combined_terms, combined_constant)
    }

    /// Return a reference to the homogeneous terms.
    pub fn terms_ref(&self) -> &[Mon<T>] {
        &self.terms
    }

    /// Return a mutable reference to the homogeneous terms.
    pub fn terms_mut(&mut self) -> &mut [Mon<T>] {
        &mut self.terms
    }

    /// Return a reference to the constant term
    pub fn constant_ref(&self) -> &T {
        &self.constant
    }

    /// Return a mutable reference to the constant term
    pub fn constant_mut(&mut self) -> &mut T {
        &mut self.constant
    }

    /// Modify the homogeneous terms
    pub fn modify_terms(&mut self, f: impl Fn(&T) -> T) {
        self.terms_mut()
            .iter_mut()
            .for_each(|term| term.coeff = f(&term.coeff))
    }

    /// Modify the constant term
    pub fn modify_constant(&mut self, f: impl Fn(&T) -> T) {
        self.constant = f(&self.constant)
    }

    /// Negate the relation, e.g. turn x > 0 into x <= 0
    pub fn negate(self) -> Option<Self> {
        self.constraint_type
            .negate()
            .map(|negated_constraint| Self {
                constraint_type: negated_constraint,
                ..self
            })
    }
}

/// Combine and sort terms by variable
///
/// pre-condition: none
/// post-condition: terms are sorted by variable and have non-zero coefficients
pub fn combine_terms_helper(terms: &[Mon<Rational>]) -> Vec<Mon<Rational>> {
    let mut map = HashMap::new();
    for term in terms.iter() {
        map.entry(term.var)
            .and_modify(|c| *c += &term.coeff)
            .or_insert(term.coeff.clone());
    }
    let mut new_terms: Vec<Mon<Rational>> = map
        .iter()
        .filter(|(_, c)| !c.is_zero())
        .map(|(idx, c)| Mon::new(c.clone(), *idx))
        .collect();
    new_terms.sort_by_key(|a| a.var);
    new_terms
}

impl Rel<Rational> {
    /// Combine and sort the relation's terms by variable
    ///
    /// pre-condition: none
    /// post-condition: terms are sorted by variable and have non-zero coefficients
    pub fn combine_terms(&mut self) {
        self.terms = combine_terms_helper(&self.terms);
    }

    /// Rewrite self to an equivalent (in)equality whose initial term has positive coefficient.
    ///
    /// pre-condition: terms have been combined
    /// post-conditions:
    ///   - self.terms.is_empty() || self.terms[0].coeff > 0
    ///   - if self.constraint == Eq then self'.contraint == Eq
    ///   - if self.constraint == Lq and self.terms[0].coeff < 0 then self'.contraint == Ge
    ///   - if self.constraint == Ge and self.terms[0].coeff < 0 then self'.contraint == Le
    ///
    fn make_initial_term_positive(&mut self) {
        if self.terms.is_empty() || self.terms[0].coeff_pos() {
            return;
        }
        for term in self.terms.iter_mut() {
            term.coeff = -&term.coeff;
        }
        self.constant = -&self.constant;
        self.constraint_type = self.constraint_type.reverse();
    }

    /// Clear denominators and reduce so that they are integral and relatively prime
    fn make_integral(&mut self) {
        // compute the lcm of the coefficients and constant
        // l = lcm(d_1, d_2, ..., d_n, c)
        let mut tmp_lcm = self.constant.denominator().clone().into();
        for term in self.terms.iter() {
            tmp_lcm = utils::lcm(&tmp_lcm, &term.coeff.denominator().clone().into());
        }

        // clear denominators
        // multiply by l: sum (n_i * (l / d_i)) x_i <= b * (l / c)
        for term in self.terms.iter_mut() {
            term.coeff *= &Rational::from(tmp_lcm.clone());
        }
        self.constant *= &Rational::from(tmp_lcm);

        // When there are terms with non-zero coefficients, compute overall gcd
        // of the now integral coefficients and constant g = gcd(n_i (l / d_i), ... b * (l / c))
        if !self.terms.is_empty() {
            debug_assert!(self.terms.iter().all(|t| t.coeff.is_int()) && self.constant.is_int());
            let mut gcd = self.terms[0].coeff.numerator().abs();
            for term in self.terms.iter() {
                gcd = gcd.gcd(term.coeff.numerator()).into();
                if gcd == Integer::ONE {
                    // common enough case to break early
                    break;
                }
            }
            gcd = gcd.gcd(self.constant.numerator()).into();

            // reduce: ensures that the coefficients and constant are relatively prime
            // divide all coefficients by g
            if gcd != Integer::ONE {
                for term in self.terms.iter_mut() {
                    term.coeff /= Rational::from(gcd.clone());
                }
                self.constant /= Rational::from(gcd);
            }
        }
    }

    /// Normalize self
    ///
    /// Normalized means:
    /// - there is at least one term on the homogeneous side
    /// - term variables are unique and in order
    /// - coefficients a_i are integers, mutually relatively prime, and != 0
    /// - the leading coefficient of the terms is > 0
    ///
    /// Note: Structural and mathematical equality agree once a relation is normalized,
    /// but not in general.
    pub fn normalize(&mut self) {
        self.combine_terms();
        self.make_initial_term_positive();
        self.make_integral();
    }

    /// Determine if self is normalized, independent of the `normalize` method
    pub fn is_normalized(&self) -> bool {
        // sorted by variable index
        if !self.terms.is_sorted() {
            return false;
        }
        // unique variables
        if !self.terms.windows(2).all(|w| w[0] != w[1]) {
            return false;
        }
        // non-zero integer coefficients
        if !self
            .terms
            .iter()
            .all(|t| t.coeff.is_int() && !t.coeff_zero())
        {
            return false;
        }
        // either empty term list, or leading coefficient > 0
        if !(self.terms.is_empty() || self.terms.first().unwrap().coeff_pos()) {
            return false;
        }
        true
    }

    /// Determine if the relation is trivially sat because its term list is empty, e.g. 0 <= 5.
    ///
    /// Returns `true` if the test is conclusively true and `false` if either it's
    /// either conclusively false, or we can't tell because it's not normalized.
    ///
    /// This is used as a simple pre-processing step when building an [LRASolver] from the frontend.
    pub fn is_trivial_sat(&self) -> bool {
        self.terms.is_empty() && self.constraint_type.test_zero(&self.constant)
    }

    /// Determine if the relation is trivially unsat because its term list is empty, e.g. 0 <= -1
    ///
    /// Returns `true` if the test is conclusively true and `false` if either it's
    /// either conclusively false, or we can't tell because it's not normalized.
    ///
    /// This is used as a simple pre-processing step when building an [LRASolver] from the frontend.
    pub fn is_trivial_unsat(&self) -> bool {
        self.terms.is_empty() && !self.constraint_type.test_zero(&self.constant)
    }

    /// Determine if the two (in)equalities are mathematically equivalent
    ///
    /// This is potentially expensive since it clones both relations; currently only used in tests.
    pub fn equivalent(&self, other: &Self) -> bool {
        let mut tmp_self = self.clone();
        let mut tmp_other = other.clone();
        tmp_self.normalize();
        tmp_other.normalize();
        tmp_self == tmp_other
    }

    /// Convert relation bounds over the rationals to bounds over [QDelta].
    ///
    /// Replacing bounds for strict constraint types with non-strict bounds is done, as well as simply
    /// injecting rational bounds for already non-strict constraint types.
    fn to_qdelta_bounds(&self) -> Bounds<QDelta> {
        let constant = self.constant.clone();
        match self.constraint_type {
            // non-strict relations are not adjusted by δ
            Constraint::Eq => Bounds::new(Some(constant.clone()), Some(constant)).inject_bounds(), // s = c <=> c <= s && s <= c
            Constraint::Le => Bounds::below_of(constant).inject_bounds(),
            Constraint::Ge => Bounds::above_of(constant).inject_bounds(),
            // strict relations are adjusted either down or up by δ
            Constraint::Lt => Bounds::below_of(Into::<QDelta>::into(constant) - QDelta::DELTA),
            Constraint::Gt => Bounds::above_of(Into::<QDelta>::into(constant) + QDelta::DELTA),
        }
    }
}

/// System of normalized linear (in)equalities.
#[derive(Debug)]
pub struct LinearSystem {
    ctx: ConvContext,
}

impl LinearSystem {
    /// Create a normalized linear system from a vector of relations.
    ///
    /// Normalization is used downstream in order to share bounds/rows in the tableau.
    /// Simple pre-processing is done to detect trivially sat relations and remove them,
    /// as well as trivially unsat relations. If a trivially unsat relation is found, it
    /// alone is used to construct the system. Simplex on the system will immediately return
    /// INFEASIBLE.
    pub fn new(ctx: ConvContext) -> Self {
        LinearSystem { ctx }
    }

    fn get_relations(&self) -> impl Iterator<Item = (&Rel<Rational>, &Var)> {
        self.ctx.get_relations()
    }

    /// Return the system variables as a set of Var(id)
    ///
    /// Note: the returned set is in general a subset of all the variables that
    /// appear in asserted theory literals in the frontend; in particular, if a variable
    /// is eliminated during term -> relation conversion or preprocessing.
    fn var_id_set(&self) -> HashSet<Var> {
        let mut result = HashSet::new();
        self.get_relations()
            .flat_map(|(rel, _)| rel.terms.iter())
            .for_each(|term| {
                let _ = result.insert(term.var);
            });
        result
    }

    /// Returns the number of relations in the system.
    pub fn num_relations(&self) -> usize {
        self.ctx.num_relations()
    }

    /// Create a high-level tableau from the system.
    ///
    /// # Choices:
    ///
    ///   * Non-basic variables are created from the system variables with same id.
    ///     They are ordered according to their (sorted) id's which are unique due to normalization.
    ///   * Basic variables are given new variable ids starting from the maximum non-basic variable id + 1
    ///     and incrementing by 1 for each corresponding relation.
    ///   * Basic variables are ordered according to the relations stored in the system, but after
    ///     all the non-basic variables. The order integer values equal their variable id.
    ///
    /// The three choices above are made to ensure that the ordering of all variables is total.
    ///
    /// # Arguments:
    ///
    ///   * `relation_bounds` - if true, set bounds on slack variables using the relations bounds.
    ///     Otherwise, leave slack variables unbounded.
    ///
    /// TODO: implement bounds refinement for relations with shared (normalized) terms.
    /// TODO: revisit basic/non-basic variable ordering. Current is arbitrary.
    pub fn to_lra_solver(
        self,
        relation_bounds: bool,
    ) -> LinearSystemResult<LRASolver<TableauDense>> {
        // original variable id's
        let var_set = self.var_id_set();
        let mut var_ids: Vec<Var> = var_set.iter().copied().collect();
        if var_ids.is_empty() {
            return Err(LinearSystemError(
                "no variables in the linear system".to_string(),
            ));
        }
        var_ids.sort();
        // map variable ID -> tableau column
        let var_id_col_map: HashMap<Var, usize> =
            var_ids.iter().enumerate().map(|(i, v)| (*v, i)).collect();

        let non_basic: Vec<VarInfo<QDelta>> = var_ids
            .iter()
            .enumerate()
            // position in variable order == variable id
            .map(|(i, v)| VarInfo::new(*v, Owner::NonBasic(i)))
            .collect();

        // Basic variables correspond to relations; their association is tracked in the context.
        // Relations and their variables have a fixed order in the context. The order is used here
        // to set row ownership.
        //
        // Bounds over the rationals are converted to bounds over the [QDelta].
        let basic: Vec<VarInfo<QDelta>> = self
            .ctx
            .get_relations()
            .enumerate()
            .map(|(i, (rel, var))| {
                let bounds = if relation_bounds {
                    rel.to_qdelta_bounds()
                } else {
                    Bounds::unbounded()
                };
                VarInfo::new(
                    // TODO: to_lra_solver: basic variables can sometimes be inferred integral
                    *var,
                    Owner::Basic(i),
                )
                .with_bounds(bounds)
            })
            .collect();

        // Build row vectors from a relation:
        //
        // Example:
        // var_ids = (0, 3, 5)
        // x0 <= 5       --> <1, 0, 0>
        // x0 + x3 <= 5  --> <1, 1, 0>
        // 0 <= x3 - x5  --> <0, 1, -1>
        //
        // time complexity is expected worst case O(#relations * #var)
        let mut equations: Vec<Vec<Rational>> = Vec::new();
        let nvars = var_ids.len();
        for (rel, _) in self.ctx.get_relations() {
            let mut row = vec![Rational::ZERO; nvars];
            for t in rel.terms_ref() {
                if var_set.contains(&t.var) {
                    let col = var_id_col_map.get(&t.var).unwrap();
                    if !t.coeff_zero() {
                        row[*col] = t.coeff.clone();
                    }
                }
            }
            equations.push(row);
        }
        // all rows should have the same length: nvars
        debug_assert!(equations.iter().all(|r| r.len() == nvars));
        LRASolver::from_eqs(basic, non_basic, equations, self.ctx)
            .map_err(|e| LinearSystemError(format!("error building tableau: {}", e)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::arithmetic::lia::{
        context::ConvContext,
        linear_system::{LinearSystem, Mon, Rel},
        lra_solver::LRASolver,
        solver_result::SolverDecision,
        tableau_dense::TableauDense,
        types::{rbig, Rational},
        variables::{Var, VarType},
    };

    #[test]
    fn monomial_coeffs() {
        // test a positive monomial
        let five_x0: Mon<Rational> = Mon::new(5, Var::real(0));
        assert!(five_x0.coeff_pos());
        assert!(!five_x0.coeff_zero());
        assert!(!five_x0.coeff_neg());

        // test a negative monomial
        let neg_five_x0: Mon<Rational> = Mon::new(-5, Var::real(0));
        assert!(!neg_five_x0.coeff_pos());
        assert!(!neg_five_x0.coeff_zero());
        assert!(neg_five_x0.coeff_neg());

        // test a zero coefficient
        let zero_x0: Mon<Rational> = Mon::new(0, Var::real(0));
        assert!(!zero_x0.coeff_pos());
        assert!(zero_x0.coeff_zero());
        assert!(!zero_x0.coeff_neg());
    }

    #[test]
    fn relation_constants() {
        let mut rel: Rel<Rational> = Rel::mk_le(vec![Mon::new(1, Var::real(0))], -1); // x_0 <= -1
        assert_eq!(rel.constant_ref(), &rbig!(-1));
        rel.modify_constant(|c| c * rbig!(-1));
        assert_eq!(rel.constant_ref(), &rbig!(1));
    }

    #[test]
    fn normalized_inequality_eq() {
        let five_x0 = Mon::new(5, Var::real(0));
        let rel1 = Rel::mk_le(vec![five_x0.clone()], 0); // 5 x_0 <= 0
        let rel2 = Rel::mk_le(vec![five_x0.clone()], 0); // 5 x_0 <= 0
        let rel3 = Rel::mk_eq(vec![five_x0], 0); // 5 x_0 = 0
        let rel4 = Rel::mk_le(vec![Mon::new(3, Var::real(0))], 0); // 3 x_0 <= 0
        let rel5 = Rel::mk_eq(vec![Mon::new(3, Var::real(0))], 0); // 3 x_0 <= 1
        assert!(rel1.equivalent(&rel2));
        assert!(!rel1.equivalent(&rel3)); // = vs. <=
        assert_ne!(rel1, rel4); // not structurally =, but equivalent
        assert!(rel1.equivalent(&rel4));
        assert_ne!(rel1, rel5); // neither structurally =, nor equivalent
        assert!(!rel4.equivalent(&rel5));
    }

    #[test]
    fn combine_terms_one_var() {
        let rel = Rel::mk_le(vec![Mon::new(5, Var::real(0))], 0); // 5 x_0 <= 0
        let mut split_rel = Rel::mk_le(
            vec![
                Mon::new(2, Var::real(0)),
                Mon::new(4, Var::real(0)),
                Mon::new(-1, Var::real(0)),
            ],
            0,
        ); // 2 x_0 + 4 x_0 - x_0 <= 0
        assert_ne!(rel, split_rel);

        split_rel.combine_terms();
        assert_eq!(rel, split_rel);
    }

    #[test]
    fn combine_terms_multiple_var() {
        let combined_rel = Rel::mk_le(
            vec![Mon::new(5, Var::real(0)), Mon::new(3, Var::real(1))],
            0,
        ); // 5 x_0 + 3 x_1 <= 0
        let mut uncombined_rel = Rel::mk_le(
            vec![
                Mon::new(3, Var::real(1)),
                Mon::new(1, Var::real(0)),
                Mon::new(0, Var::real(1)),
                Mon::new(1, Var::real(0)),
                Mon::new(3, Var::real(0)),
            ],
            0,
        ); // 3 x_1 + x_0 + 0 x_1 + x_0 + 3 x_0 + <= 0
        assert_ne!(combined_rel, uncombined_rel);

        uncombined_rel.combine_terms();
        assert_eq!(combined_rel, uncombined_rel);
    }

    #[test]
    fn make_initial_term_positive() {
        let mut rel: Rel<Rational> = Rel::mk_le(
            vec![Mon::new(-5, Var::real(0)), Mon::new(3, Var::real(1))],
            1,
        ); // -5 x_0 + 3 x_1 <= 1
        assert!(rel.terms[0].coeff_neg());
        assert!(rel.terms[1].coeff_pos());
        assert!(rel.constant > Rational::ZERO);
        assert_eq!(rel.constraint_type, Constraint::Le);

        rel.make_initial_term_positive(); // re-written to: -1 <= 5 x_0 - 3 x_1
        assert!(rel.terms[0].coeff_pos());
        assert!(rel.terms[1].coeff_neg());
        assert!(rel.constant < Rational::ZERO);
        assert_eq!(rel.constraint_type, Constraint::Ge);

        let expected_rel: Rel<Rational> = Rel::mk_ge(
            vec![Mon::new(5, Var::real(0)), Mon::new(-3, Var::real(1))],
            -1,
        ); // -5 x_0 + 3 x_1 <= 0
        assert_eq!(rel, expected_rel);
    }

    #[test]
    fn normalize_two_var() {
        // -5/3 x_0 + 3 x_1 + 0 x_0 <= 1
        let mut rel: Rel<Rational> = Rel::mk_le(
            vec![
                Mon::new(rbig!(-5 / 3), Var::real(0)),
                Mon::new(3, Var::real(1)),
                Mon::new(0, Var::real(0)),
            ],
            1,
        );
        rel.normalize();
        assert!(rel.is_normalized());

        // -5 x_0 + 9 x_1 <= 3 --> -3 <= 5 x_0 - 9 x_1
        let expected_rel: Rel<Rational> = Rel::mk_ge(
            vec![Mon::new(5, Var::real(0)), Mon::new(-9, Var::real(1))],
            -3,
        );
        assert_eq!(rel, expected_rel);

        // same test
        assert!(rel.equivalent(&expected_rel));
    }

    #[test]
    fn equivalent_equalities() {
        // 1/2 x_1 - 1/3 x_2 + 1/5 x_3 = 1/7
        let rel: Rel<Rational> = Rel::mk_eq(
            vec![
                Mon::new(rbig!(1 / 2), Var::real(1)),
                Mon::new(rbig!(-1 / 3), Var::real(2)),
                Mon::new(rbig!(1 / 5), Var::real(3)),
            ],
            rbig!(1 / 7),
        );
        assert!(!rel.is_normalized()); // not integral

        // mutually relatively prime:
        // 3 * 5 * 7 = 105
        // 2 * 5 * 7 = 70
        // 2 * 3 * 7 = 42
        // 2 * 3 * 5 = 30
        //
        // 105 x_1 - 70 x_2 + 42 x_3 = 30
        let normed_rel_pos_leading: Rel<Rational> = Rel::mk_eq(
            vec![
                Mon::new(rbig!(105), Var::real(1)),
                Mon::new(rbig!(-70), Var::real(2)),
                Mon::new(rbig!(42), Var::real(3)),
            ],
            rbig!(30),
        );
        // this one is normalized, but rel is not
        assert!(normed_rel_pos_leading.is_normalized());
        assert!(rel.equivalent(&normed_rel_pos_leading));

        // -105 x_1 + 70 x_2 - 42 x_3 = -30
        let normed_rel_neg_leading: Rel<Rational> = Rel::mk_eq(
            vec![
                Mon::new(rbig!(-105), Var::real(1)),
                Mon::new(rbig!(70), Var::real(2)),
                Mon::new(rbig!(-42), Var::real(3)),
            ],
            rbig!(-30),
        );
        assert!(!normed_rel_neg_leading.is_normalized()); // negative leading coefficient
        assert!(rel.equivalent(&normed_rel_neg_leading));
    }

    #[test]
    fn addend_construction() {
        // Test creating addends
        let term_addend: Addend<Rational> = Addend::term(5, Var::real(0));
        let const_addend: Addend<Rational> = Addend::constant(10);

        match term_addend {
            Addend::Term(mon) => {
                assert_eq!(mon.var, Var::real(0));
                assert_eq!(mon.coeff, rbig!(5));
            }
            _ => panic!("Expected Term variant"),
        }

        match const_addend {
            Addend::Constant(val) => assert_eq!(val, rbig!(10)),
            _ => panic!("Expected Constant variant"),
        }
    }

    #[test]
    fn relation_from_addends() {
        // Test creating a relation from addends: 2*x0 + 3*x1 + 5 = 0
        // This should become: 2*x0 + 3*x1 = -5
        let addends = vec![
            Addend::term(2, Var::real(0)),
            Addend::term(3, Var::real(1)),
            Addend::constant(5),
        ];

        let rel: Rel<i32> = Rel::from_addends_lhs_rhs(addends, Constraint::Eq, vec![]);

        assert_eq!(rel.constraint_type, Constraint::Eq);
        assert_eq!(rel.terms.len(), 2);
        assert_eq!(rel.terms[0].var, Var::real(0));
        assert_eq!(rel.terms[0].coeff, 2);
        assert_eq!(rel.terms[1].var, Var::real(1));
        assert_eq!(rel.terms[1].coeff, 3);
        assert_eq!(rel.constant, -5);
    }

    #[test]
    fn relation_from_addends_multiple_constants() {
        // Test with multiple constants: x0 + 2 + 3 <= 0
        // This should become: x0 <= -5
        let addends = vec![
            Addend::term(1, Var::real(0)),
            Addend::constant(2),
            Addend::constant(3),
        ];

        let rel: Rel<i32> = Rel::from_addends_lhs_rhs(addends, Constraint::Le, vec![]);

        assert_eq!(rel.constraint_type, Constraint::Le);
        assert_eq!(rel.terms.len(), 1);
        assert_eq!(rel.terms[0].var, Var::real(0));
        assert_eq!(rel.terms[0].coeff, 1);
        assert_eq!(rel.constant, -5);
    }

    #[test]
    fn relation_from_addends_rational() {
        // Test with rational coefficients: (1/2)*x0 + (3/4)*x1 + 1/3 = 0
        let addends = vec![
            Addend::term(rbig!(1 / 2), Var::real(0)),
            Addend::term(rbig!(3 / 4), Var::real(1)),
            Addend::constant(rbig!(1 / 3)),
        ];

        let rel: Rel<Rational> = Rel::from_addends_lhs_rhs(addends, Constraint::Eq, vec![]);

        assert_eq!(rel.constraint_type, Constraint::Eq);
        assert_eq!(rel.terms.len(), 2);
        assert_eq!(rel.terms[0].var, Var::real(0));
        assert_eq!(rel.terms[0].coeff, rbig!(1 / 2));
        assert_eq!(rel.terms[1].var, Var::real(1));
        assert_eq!(rel.terms[1].coeff, rbig!(3 / 4));
        assert_eq!(rel.constant, rbig!(-1 / 3));
    }

    #[test]
    fn relation_from_addends_lhs_rhs() {
        // Test creating a relation from LHS and RHS: 2*x0 + 3 <= 4*x1 + 5
        // This should become: 2*x0 - 4*x1 <= 5 - 3, i.e., 2*x0 - 4*x1 <= 2
        let lhs = vec![Addend::term(2, Var::real(0)), Addend::constant(3)];
        let rhs = vec![Addend::term(4, Var::real(1)), Addend::constant(5)];

        let rel: Rel<i32> = Rel::from_addends_lhs_rhs(lhs, Constraint::Le, rhs);

        assert_eq!(rel.constraint_type, Constraint::Le);
        assert_eq!(rel.terms.len(), 2);
        assert_eq!(rel.terms[0].var, Var::real(0));
        assert_eq!(rel.terms[0].coeff, 2);
        assert_eq!(rel.terms[1].var, Var::real(1));
        assert_eq!(rel.terms[1].coeff, -4);
        assert_eq!(rel.constant, 2);
    }

    #[test]
    fn relation_from_addends_lhs_rhs_equality() {
        // Test equality: x0 + 2 = 3*x1 + 7
        // This should become: x0 - 3*x1 = 7 - 2, i.e., x0 - 3*x1 = 5
        let lhs = vec![Addend::term(1, Var::real(0)), Addend::constant(2)];
        let rhs = vec![Addend::term(3, Var::real(1)), Addend::constant(7)];

        let rel: Rel<i32> = Rel::from_addends_lhs_rhs(lhs, Constraint::Eq, rhs);

        assert_eq!(rel.constraint_type, Constraint::Eq);
        assert_eq!(rel.terms.len(), 2);
        assert_eq!(rel.terms[0].var, Var::real(0));
        assert_eq!(rel.terms[0].coeff, 1);
        assert_eq!(rel.terms[1].var, Var::real(1));
        assert_eq!(rel.terms[1].coeff, -3);
        assert_eq!(rel.constant, 5);
    }

    #[test]
    fn relation_from_addends_lhs_rhs_only_constants() {
        // Test with only constants: 10 >= 5
        // This should become: 0 >= 5 - 10, i.e., 0 >= -5
        let lhs = vec![Addend::constant(10)];
        let rhs = vec![Addend::constant(5)];

        let rel: Rel<i32> = Rel::from_addends_lhs_rhs(lhs, Constraint::Ge, rhs);

        assert_eq!(rel.constraint_type, Constraint::Ge);
        assert_eq!(rel.terms.len(), 0);
        assert_eq!(rel.constant, -5);

        // Test with only constants: 5 + 3 >= 0
        let addends = vec![Addend::constant(5), Addend::constant(3)];

        let rel: Rel<i32> = Rel::from_addends_lhs_rhs(addends, Constraint::Ge, vec![]);

        assert_eq!(rel.constraint_type, Constraint::Ge);
        assert!(rel.terms.is_empty());
        assert_eq!(rel.constant, -8);
    }

    /// An basic feasible linear to solve. This tests linear system setup and solving under
    /// the fixed variable ordering chosen by the system builder.
    ///
    /// System is:
    ///   2 <=    x0 +    x1
    ///   0 <=  2 x0 + -1 x1
    ///   1 <= -1 x0 +  2 x1
    ///
    #[test]
    fn solve_basic_feasible_system() {
        let _ = env_logger::builder().is_test(true).try_init();

        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let _s1 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x), Mon::new(1, y)], 2));
        let _s2 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(2, x), Mon::new(-1, y)], 0));
        let _s3 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(-1, x), Mon::new(2, y)], 1));

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(true).expect("failed to build solver");

        assert!(solver.is_valid());
        let result = solver.solve().expect("simplex failed");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
    }

    /// A trivial, completely unbounded feasible linear system to solve. This tests the unbounded
    /// linear system setup and incremental bound assertion/backtracking.
    ///
    /// System is:
    ///
    ///   -\infinity <    x0 +    x1 < +\infinity
    ///   -\infinity <  2 x0 + -1 x1 < +\infinity
    ///
    /// which is satisfiable for every x0, x1.
    ///
    #[test]
    fn solve_unbounded_feasible_system() {
        let _ = env_logger::builder().is_test(true).try_init();

        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        // note that the constants and inequality directions get ignored when the
        // unbounded system is created
        let _s1 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x), Mon::new(1, y)], 2));
        let _s2 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(2, x), Mon::new(-1, y)], 0));

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(false).expect("failed to build solver");

        assert!(solver.is_valid());
        let result = solver.solve().expect("simplex failed");
        // TODO: check all assignments are ZERO
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
        if let SolverDecision::FEASIBLE(assg) = result {
            assert!(assg.iter().all(|(_, val)| val.is_zero()));
        } else {
            unreachable!("unexpected test result");
        }

        // Incrementally assert a new bound and solve again
        let level = solver.set_backtrack();
        assert_eq!(
            solver
                .assert_upper(&x, &1i32.into())
                .expect("bound assertion failed"),
            Some(true)
        );
        let result = solver.solve().expect("simplex failed");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
        if let SolverDecision::FEASIBLE(assg) = result {
            assert!(assg.iter().all(|(_, val)| val.is_zero()));
        } else {
            unreachable!("unexpected test result");
        }

        // Now show that -1 is consistent with the prior unbounded state, but feasibility
        // is now unknown.
        solver.backtrack(level);
        assert_eq!(
            solver
                .assert_upper(&x, &(-1i32).into())
                .expect("bound assertion failed"),
            None
        );
    }

    /// Same infeasible system as in ex_triangle_hole_infeasible, but constructed from the relation representation.
    ///
    /// Because the linear system builder orders variables differently than the manually
    /// setup but mathematically equivalent version in `ex_triangle_hole_infeasible`, this
    /// test exercises different logic in the simplex implementation. It caught a hard-to-diagnose
    /// bug in the simplex implementation.
    ///
    /// System:
    ///   x0 <= 0,
    ///   x1 <= 0,
    ///   x1 + x0 >= 1
    ///
    #[test]
    fn solve_basic_infeasible_system() {
        let _ = env_logger::builder().is_test(true).try_init();

        let mut ctx = ConvContext::new();
        let x0 = ctx.allocate_var("x0", VarType::Real);
        let x1 = ctx.allocate_var("x1", VarType::Real);
        let _r1 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x0)], 0));
        let _r2 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x1)], 0));
        let _r3 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x1), Mon::new(1, x0)], 1));

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(true).expect("failed to build solver");
        assert!(solver.is_valid());
        assert!(matches!(
            solver.solve().expect("simplex failed"),
            SolverDecision::INFEASIBLE(_)
        ));
    }

    /// Setup a linear system corresponding to an implicant from SMT-LIB benchmark
    /// `QF_LRA/sal/carpark/Carpark2-t1-1.smt2`
    ///
    /// (= x_34 x_13)
    /// (= x_38 x_10)
    /// (= x_48 x_10)
    /// (= x_51 x_29)
    /// (= x_53 x_12)
    /// (= x_55 x_10)
    /// (= x_58 x_22)
    /// (= x_59 x_30)
    /// (= x_61 x_10)
    /// (= x_64 x_10)
    /// (= x_65 x_14)
    /// (= x_66 8)
    /// (= x_67 3)
    /// (= x_70 4)
    /// (> x_59 0)
    ///
    /// Note: this is a regression for bug in 7a004aa2c8251c5fc92d9f02773f302afe1d9ece
    #[test]
    fn solve_carpark2_t1_1_implicant() {
        let mut ctx = ConvContext::new();
        let x10 = ctx.allocate_var("x10", VarType::Real);
        let x12 = ctx.allocate_var("x12", VarType::Real);
        let x13 = ctx.allocate_var("x13", VarType::Real);
        let x14 = ctx.allocate_var("x14", VarType::Real);
        let x22 = ctx.allocate_var("x22", VarType::Real);
        let x29 = ctx.allocate_var("x29", VarType::Real);
        let x30 = ctx.allocate_var("x30", VarType::Real);
        let x34 = ctx.allocate_var("x34", VarType::Real);
        let x38 = ctx.allocate_var("x38", VarType::Real);
        let x48 = ctx.allocate_var("x48", VarType::Real);
        let x51 = ctx.allocate_var("x51", VarType::Real);
        let x53 = ctx.allocate_var("x53", VarType::Real);
        let x55 = ctx.allocate_var("x55", VarType::Real);
        let x58 = ctx.allocate_var("x58", VarType::Real);
        let x59 = ctx.allocate_var("x59", VarType::Real);
        let x61 = ctx.allocate_var("x61", VarType::Real);
        let x64 = ctx.allocate_var("x64", VarType::Real);
        let x65 = ctx.allocate_var("x65", VarType::Real);
        let x66 = ctx.allocate_var("x66", VarType::Real);
        let x67 = ctx.allocate_var("x67", VarType::Real);
        let x70 = ctx.allocate_var("x70", VarType::Real);

        let _r1 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x34), Mon::new(-1, x13)], 0));
        let _r2 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x38), Mon::new(-1, x10)], 0));
        let _r3 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x48), Mon::new(-1, x10)], 0));
        let _r4 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x51), Mon::new(-1, x29)], 0));
        let _r5 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x53), Mon::new(-1, x12)], 0));
        let _r6 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x55), Mon::new(-1, x10)], 0));
        let _r7 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x58), Mon::new(-1, x22)], 0));
        let _r8 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x59), Mon::new(-1, x30)], 0));
        let _r9 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x61), Mon::new(-1, x10)], 0));
        let _r10 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x64), Mon::new(-1, x10)], 0));
        let _r11 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x65), Mon::new(-1, x14)], 0));
        let _r12 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x66)], 8));
        let _r13 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x67)], 3));
        let _r14 = ctx.allocate_relation(Rel::mk_eq(vec![Mon::new(1, x70)], 4));
        let _r15 = ctx.allocate_relation(Rel::mk_gt(vec![Mon::new(1, x59)], 0));

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(true).expect("failed to build solver");
        assert!(solver.is_valid());
        let result = solver.solve().expect("simplex failed");
        // validate the assignment
        if let SolverDecision::FEASIBLE(assg) = result {
            // Find the value of x_59 and assert it is strictly positive
            let x_59 = assg.get(&x59).unwrap();
            assert!(
                x_59 > &Rational::ZERO,
                "expected strictly positive solution"
            );
        }
    }

    /// Solve an UNSAT 3-SAT problem
    ///
    /// (𝑥∨𝑦∨𝑧)∧(𝑥∨𝑦∨¬𝑧)∧(𝑥∨¬𝑦∨𝑧)∧(𝑥∨¬𝑦∨¬𝑧)∧(¬𝑥∨𝑦∨𝑧)∧(¬𝑥∨𝑦∨¬𝑧)∧(¬𝑥∨¬𝑦∨𝑧)∧(¬𝑥∨¬𝑦∨¬𝑧)
    ///
    /// positive x is encoded as an int term w/ coeff. 1 with bounds {0, 1}, ¬x is encoded
    /// similarly but the term is (1-x).
    ///
    /// TODO: once LIA is supported, assert that this system is INFEASIBLE
    #[test]
    fn unsat_3_sat_problem_sat_over_rationals() {
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let z = ctx.allocate_var("z", VarType::Real);

        // x,y,z bounds [0,1]
        let _r1 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x)], 1));
        let _r2 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x)], 0));
        let _r3 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, y)], 1));
        let _r4 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, y)], 0));
        let _r5 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, z)], 1));
        let _r6 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, z)], 0));

        // Clauses
        let _r7 = ctx.allocate_relation(Rel::mk_ge(
            vec![Mon::new(1, x), Mon::new(1, y), Mon::new(1, z)],
            Rational::from(1),
        ));
        let _r8 = ctx.allocate_relation(Rel::mk_ge(
            vec![Mon::new(1, x), Mon::new(1, y), Mon::new(-1, z)],
            Rational::from(0),
        ));
        let _r9 = ctx.allocate_relation(Rel::mk_ge(
            vec![Mon::new(1, x), Mon::new(-1, y), Mon::new(1, z)],
            Rational::from(0),
        ));
        let _r10 = ctx.allocate_relation(Rel::mk_ge(
            vec![Mon::new(1, x), Mon::new(-1, y), Mon::new(-1, z)],
            Rational::from(-1),
        ));
        let _r11 = ctx.allocate_relation(Rel::mk_ge(
            vec![Mon::new(-1, x), Mon::new(1, y), Mon::new(1, z)],
            Rational::from(0),
        ));
        let _r12 = ctx.allocate_relation(Rel::mk_ge(
            vec![Mon::new(-1, x), Mon::new(1, y), Mon::new(-1, z)],
            Rational::from(-1),
        ));
        let _r13 = ctx.allocate_relation(Rel::mk_ge(
            vec![Mon::new(-1, x), Mon::new(-1, y), Mon::new(1, z)],
            Rational::from(-1),
        ));
        let _r14 = ctx.allocate_relation(Rel::mk_ge(
            vec![Mon::new(-1, x), Mon::new(-1, y), Mon::new(-1, z)],
            Rational::from(-2),
        ));

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(true).expect("failed to build solver");
        assert!(solver.is_valid());
        let result = solver.solve().expect("simplex failed");
        // validate the assignment
        if let SolverDecision::FEASIBLE(assg) = result {
            // the system is feasible, but only via some values being non-integral. For example:
            //
            // x = 1 / 2
            // y = 1 / 2
            // z = 0
            //
            assert!(assg.iter().any(|(_, val)| !val.is_int()));
        } else {
            unreachable!("unexpected result");
        }
    }

    /// System is infeasible:
    ///
    /// x1 <= -1 x0 + 1  -->  x0 + x1 <= 1
    /// x1 >  -1 x0 + 1  -->  x0 + x1 > 1
    #[test]
    fn solve_system_with_strict_gt() {
        let _ = env_logger::builder().is_test(true).try_init();

        let mut ctx = ConvContext::new();
        let x0 = ctx.allocate_var("x0", VarType::Real);
        let x1 = ctx.allocate_var("x1", VarType::Real);
        let _r1 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x0), Mon::new(1, x1)], 1));
        let _r2 = ctx.allocate_relation(Rel::mk_gt(vec![Mon::new(1, x0), Mon::new(1, x1)], 1));

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(true).expect("failed to build solver");

        assert!(solver.is_valid());
        let result = solver.solve().expect("simplex failed");
        assert!(matches!(result, SolverDecision::INFEASIBLE(_)));
    }

    /// Return a setup LRA solver for the following system, satisfiable over Q but not over Z:
    ///
    /// - bounded by {y > x, y < 2/3, x > 1/3 }
    ///
    /// Initial tableau and bounds
    ///
    ///      x   y
    /// s1 | -1  1 |   0 + δ <= s1
    /// s2 |     1 |            s2 <= 2/3 - δ
    /// s3 |  1    | 1/3 + δ <= s3
    ///
    fn open_polytope_in_unit_cube() -> (LRASolver<TableauDense>, Var, Var) {
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let _r1 = ctx.allocate_relation(Rel::mk_gt(vec![Mon::new(-1, x), Mon::new(1, y)], 0));
        let _r2 = ctx.allocate_relation(Rel::mk_lt(vec![Mon::new(1, y)], rbig!(2 / 3)));
        let _r3 = ctx.allocate_relation(Rel::mk_gt(vec![Mon::new(1, x)], rbig!(1 / 3)));

        let sys = LinearSystem::new(ctx);
        let solver = sys.to_lra_solver(true).expect("failed to build solver");
        assert!(solver.is_valid());
        (solver, x, y)
    }

    /// System is composed of all strict inequalities and is feasible, but
    /// the feasible set is strictly contained in the unit cube [0,1]x[0,1]
    ///
    /// -x + y > 0
    ///      y < 2/3
    ///  x     > 1/3
    ///
    #[test]
    fn solve_strict_system_strictly_in_unit_cube() {
        let _ = env_logger::builder().is_test(true).try_init();
        let (mut solver, _x, _y) = open_polytope_in_unit_cube();
        let result = solver.solve().expect("simplex failed");
        if let SolverDecision::FEASIBLE(assg) = result {
            // the system is feasible, but only via *all* variables being non-integral
            assert!(assg.iter().all(|(_, val)| !val.is_int()));
            // So x := 11/30 and y := 7/10
        } else {
            unreachable!("unexpected result");
        }
    }

    #[test]
    fn solve_strict_system_strictly_in_unit_cube_then_assert_lower() {
        let _ = env_logger::builder().is_test(true).try_init();
        let (mut solver, x, _y) = open_polytope_in_unit_cube();
        assert!(matches!(
            solver.solve().expect("simplex failed"),
            SolverDecision::FEASIBLE(_)
        ));

        // 1. assert a lower bound on x which is tighter than the current one and
        // satisfies the current assignment.
        assert_eq!(
            solver.assert_lower(&x, &rbig!(1 / 10).into()).unwrap(),
            Some(true)
        );
        if let SolverDecision::FEASIBLE(ass) = solver.solve().expect("simplex failed") {
            assert_eq!(ass.get(&x).unwrap(), &rbig!(7 / 18));
        } else {
            unreachable!()
        }

        // 2. assert a lower bound on x which is tighter than the current one and
        // does not satisfy the current assignment, but for which the original system along
        // with the new bound is feasible.
        assert_eq!(
            solver.assert_lower(&x, &rbig!(5 / 9).into()).unwrap(),
            None, // feasibility is now unknown
        );
        // the new lower bound pushed x up to its lower bound
        if let SolverDecision::FEASIBLE(ass) = solver.solve().expect("simplex failed") {
            assert_eq!(ass.get(&x).unwrap(), &rbig!(5 / 9));
        } else {
            unreachable!()
        }

        // 3. assert a lower bound on x which is too large for the system to be feasible
        assert_eq!(
            solver.assert_lower(&x, &2i32.into()).unwrap(),
            None, // feasibility is now unknown
        );
        // system is now infeasible
        assert!(matches!(
            solver.solve().expect("simplex failed"),
            SolverDecision::INFEASIBLE(_)
        ));
    }

    #[test]
    fn solve_strict_system_strictly_in_unit_cube_then_assert_upper() {
        let _ = env_logger::builder().is_test(true).try_init();
        let (mut solver, x, y) = open_polytope_in_unit_cube();
        if let SolverDecision::FEASIBLE(ass) = solver.solve().expect("simplex failed") {
            // test x and y's values
            assert!(rbig!(1 / 3) <= *ass.get(&x).unwrap() && *ass.get(&x).unwrap() <= rbig!(2 / 3));
            assert!(rbig!(1 / 3) <= *ass.get(&y).unwrap() && *ass.get(&y).unwrap() <= rbig!(2 / 3));
        } else {
            unreachable!()
        }

        // 1. assert an upper bound on y which is tighter (199/300 < +inf) than the current
        //    one and satisfies the current assignment.
        assert_eq!(
            solver.assert_upper(&y, &rbig!(199 / 300).into()).unwrap(),
            Some(true)
        );
        if let SolverDecision::FEASIBLE(ass) = solver.solve().expect("simplex failed") {
            assert!(
                rbig!(1 / 3) <= *ass.get(&y).unwrap() && *ass.get(&y).unwrap() <= rbig!(199 / 300)
            );
        } else {
            unreachable!()
        }
        // 2. assert an upper bound on y which is tighter than the current one and
        // does not satisfy the current assignment, but for which the original system along
        // with the new bound is feasible.
        //
        // Note: the new upper bound used here is barely larger than the infimum
        // of y over the feasible set. The solver state before assert 2 may have assigned
        // an infinitesimally larger value than 1/3 so the assert method result may either
        // be None or Some(true).
        let assert_upper_2_result = solver.assert_upper(&y, &rbig!(1001 / 3000).into()).unwrap();
        assert_ne!(assert_upper_2_result, Some(false)); // either None or Some(true)

        if let SolverDecision::FEASIBLE(ass) = solver.solve().expect("simplex failed") {
            assert!(
                rbig!(1 / 3) <= *ass.get(&y).unwrap()
                    && *ass.get(&y).unwrap() <= rbig!(1001 / 3000)
            );
        } else {
            unreachable!()
        }

        // 3. assert an upper bound on x which is too small for the system to be feasible
        assert_eq!(
            solver.assert_upper(&y, &0i32.into()).unwrap(),
            None, // feasibility is now unknown
        );
        // system is now infeasible
        assert!(matches!(
            solver.solve().expect("simplex failed"),
            SolverDecision::INFEASIBLE(_)
        ));
    }

    /// Non-strict version of solve_system_strictly_in_unit_cube
    ///
    /// This test solves the system as in the previous, but also executes branch-and-bound
    /// to try to find an integral assignment for variable 0, which doesn't exist. Hence the
    /// system is infeasible over Z.
    #[test]
    fn solve_non_strict_lia_system_strictly_in_unit_cube() {
        let _ = env_logger::builder().is_test(true).try_init();

        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let _r1 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(-1, x), Mon::new(1, y)], 0));
        let _r2 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, y)], rbig!(2 / 3)));
        let _r3 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x)], rbig!(1 / 3)));

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(true).unwrap();

        let result = solver.solve().unwrap();
        if let SolverDecision::FEASIBLE(assg) = result {
            // the system is feasible, but only via *all* original variables being non-integral
            assert!(!assg.get(&x).unwrap().is_int() && !assg.get(&y).unwrap().is_int());
            // x = 1/3 is the specific solution found by simplex
            assert_eq!(assg.get(&x).unwrap(), &rbig!(1 / 3));
        } else {
            unreachable!("unexpected result");
        }

        // Branch based on the rational assignment x = 1/3:
        //   S_0 := S.update(x <= 0)
        //   S_1 := S.update(x >= 1)
        //  both of these are infeasible over Q, hence S is infeasible over Z.

        // Solve S_0
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let _r1 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(-1, x), Mon::new(1, y)], 0));
        let _r2 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, y)], rbig!(2 / 3)));
        let _r3 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x)], rbig!(1 / 3)));
        let _r4 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x)], rbig!(0))); // new bound x <= 0

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(true).unwrap();
        assert!(matches!(
            solver.solve().unwrap(),
            SolverDecision::INFEASIBLE(_)
        ));

        // Solve S_1
        let mut ctx = ConvContext::new();
        let x = ctx.allocate_var("x", VarType::Real);
        let y = ctx.allocate_var("y", VarType::Real);
        let _r1 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(-1, x), Mon::new(1, y)], 0));
        let _r2 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, y)], rbig!(2 / 3)));
        let _r3 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x)], rbig!(1 / 3)));
        let _r4 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, y)], rbig!(1))); // new bound y >= 1

        let sys = LinearSystem::new(ctx);
        let mut solver = sys.to_lra_solver(true).unwrap();
        assert!(matches!(
            solver.solve().unwrap(),
            SolverDecision::INFEASIBLE(_)
        ));
    }
    /// Test that trivially satisfiable relations are included in the system.
    ///
    /// System:
    ///   x0 + x1 <= 5       (non-trivial relation)
    ///   0 <= 5             (trivially satisfiable relation)
    ///   x0 - x1 >= -2      (non-trivial relation)
    ///   x0 - x0 <= 0       (trivially satisfiable relation)
    ///
    /// The resulting system should have all 4 relations, as the new approach
    /// doesn't automatically filter trivially satisfiable relations.
    #[test]
    fn test_trivially_sat_relation_removal() {
        let _ = env_logger::builder().is_test(true).try_init();

        let mut ctx = ConvContext::new();
        let x0 = ctx.allocate_var("x0", VarType::Real);
        let x1 = ctx.allocate_var("x1", VarType::Real);
        let _r1 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x0), Mon::new(1, x1)], 5));
        let _r2 = ctx.allocate_relation(Rel::mk_le(vec![], 5)); // Trivially satisfiable: 0 <= 5
        let _r3 = ctx.allocate_relation(Rel::mk_ge(vec![Mon::new(1, x0), Mon::new(-1, x1)], -2));
        let _r4 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x0), Mon::new(-1, x0)], 0));

        let sys = LinearSystem::new(ctx);

        // Assert that the resulting system has all 4 relations
        assert_eq!(
            sys.num_relations(),
            4,
            "Expected 4 relations in the new approach"
        );

        // Verify that the system is still solvable
        let mut solver = sys.to_lra_solver(true).expect("failed to build tableau");
        assert!(solver.is_valid());
        let result = solver.solve().expect("simplex failed");
        assert!(matches!(result, SolverDecision::FEASIBLE(_)));
    }

    /// Test that trivially contradictory constraints result in a system that can still
    /// be solved (the solver will detect the infeasibility).
    ///
    /// System:
    ///   x0 + x1 <= 5       (non-trivial relation)
    ///   0 > 1              (trivially unsat - using empty terms)
    ///
    /// The resulting system should have both relations, and the solver should
    /// detect that it's infeasible.
    #[test]
    fn test_trivially_unsat_relation_preprocessing() {
        let _ = env_logger::builder().is_test(true).try_init();

        let mut ctx = ConvContext::new();
        let x0 = ctx.allocate_var("x0", VarType::Real);
        let x1 = ctx.allocate_var("x1", VarType::Real);
        let _r1 = ctx.allocate_relation(Rel::mk_le(vec![Mon::new(1, x0), Mon::new(1, x1)], 5));
        let _r2 = ctx.allocate_relation(Rel::mk_gt(vec![], 1)); // 0 > 1 - directly trivially unsat

        let sys = LinearSystem::new(ctx);
        assert_eq!(sys.num_relations(), 2, "Expected 2 relations");

        // Verify that the system is infeasible
        let mut solver = sys.to_lra_solver(true).expect("failed to build solver");
        let result = solver.solve().expect("solver failed");
        assert!(matches!(result, SolverDecision::INFEASIBLE(_)));
    }
}
