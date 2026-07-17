// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! Goal-relative syntactic distances for quantifier-instantiation prioritization.
//!
//! This is a term-level adaptation of SHAKE's assertion-distance heuristic:
//! assertions are reached in layers through shared user-defined symbols, starting
//! from the goal assertion. Every original subterm inherits the minimum distance
//! of an assertion containing it.

use std::collections::BTreeSet;

use crate::utils::DeterministicHashMap;
use yaspar_ir::ast::ATerm::*;
use yaspar_ir::ast::alg::{CheckIdentifier, IdentifierKind};
use yaspar_ir::ast::{Attribute, Context, Repr, Term};

pub(crate) type SyntacticDistance = u32;

#[derive(Debug, Clone)]
pub(crate) struct GoalDistance {
    user_symbols: BTreeSet<String>,
    symbol_distances: DeterministicHashMap<String, SyntacticDistance>,
    term_distances: DeterministicHashMap<u64, SyntacticDistance>,
    unreachable_distance: SyntacticDistance,
}

#[derive(Debug, Clone)]
struct FormulaState {
    visible_symbols: BTreeSet<String>,
    quantifiers: Vec<QuantifierState>,
}

#[derive(Debug, Clone)]
struct QuantifierState {
    patterns: Vec<BTreeSet<String>>,
    hidden_body: Term,
}

impl GoalDistance {
    /// Build distances for `assertions`, treating `goal_index` as distance zero.
    pub(crate) fn new(assertions: &[Term], goal_index: usize, context: &Context) -> Self {
        assert!(
            goal_index < assertions.len(),
            "goal assertion index must be in bounds"
        );

        let user_symbols = user_defined_symbols(context);
        let mut formula_states: Vec<FormulaState> = assertions
            .iter()
            .map(|term| initialize_formula_state(term, &user_symbols))
            .collect();

        let mut assertion_distances = vec![None; assertions.len()];
        assertion_distances[goal_index] = Some(0);

        let mut reached_symbols = formula_states[goal_index].visible_symbols.clone();
        let mut symbol_distances = DeterministicHashMap::default();
        for symbol in &reached_symbols {
            symbol_distances.insert(symbol.clone(), 0);
        }

        let mut round: SyntacticDistance = 1;
        loop {
            let mut changed = false;
            let mut accumulated_symbols = BTreeSet::new();

            for (index, state) in formula_states.iter_mut().enumerate() {
                // SHAKE delays newly exposed symbols until the next round so
                // assertion order cannot affect distances.
                let previously_visible = state.visible_symbols.clone();
                let expanded = expand_matching_quantifiers(state, &reached_symbols, &user_symbols);
                changed |= expanded;
                let relevant = expanded || !state.visible_symbols.is_disjoint(&reached_symbols);

                if relevant {
                    if assertion_distances[index].is_none() {
                        assertion_distances[index] = Some(round);
                        changed = true;
                    }
                    accumulated_symbols.extend(previously_visible);
                }
            }

            let new_symbols: BTreeSet<String> = accumulated_symbols
                .difference(&reached_symbols)
                .cloned()
                .collect();
            for symbol in &new_symbols {
                symbol_distances.entry(symbol.clone()).or_insert(round);
            }
            changed |= !new_symbols.is_empty();
            reached_symbols.extend(accumulated_symbols);

            if !changed {
                break;
            }
            round = round.saturating_add(1);
        }

        // Keep unreachable terms finite so priorities can be composed without
        // overflow. The extra layer leaves a clear gap after the last reached one.
        let unreachable_distance = round.saturating_add(1);
        let mut term_distances = DeterministicHashMap::default();
        for (index, assertion) in assertions.iter().enumerate() {
            let distance = assertion_distances[index].unwrap_or(unreachable_distance);
            record_subterm_distances(assertion, distance, &mut term_distances);
        }

        Self {
            user_symbols,
            symbol_distances,
            term_distances,
            unreachable_distance,
        }
    }

    /// Distance for an original or dynamically-created term.
    ///
    /// Original subterms use their assertion provenance. A new term is one
    /// layer beyond its nearest reached symbol, matching SHAKE's next-round rule.
    pub(crate) fn term_distance(&self, term: &Term) -> SyntacticDistance {
        if let Some(distance) = self.term_distances.get(&term.uid()) {
            return *distance;
        }

        symbols_in_term(term, &self.user_symbols)
            .iter()
            .filter_map(|symbol| self.symbol_distances.get(symbol))
            .min()
            .map(|distance| distance.saturating_add(1))
            .unwrap_or(self.unreachable_distance)
            .min(self.unreachable_distance)
    }

    #[cfg(test)]
    fn unreachable_distance(&self) -> SyntacticDistance {
        self.unreachable_distance
    }
}

fn initialize_formula_state(term: &Term, user_symbols: &BTreeSet<String>) -> FormulaState {
    let mut state = FormulaState {
        visible_symbols: BTreeSet::new(),
        quantifiers: vec![],
    };
    collect_formula_state(term, user_symbols, &mut state);
    state
}

fn collect_formula_state(term: &Term, user_symbols: &BTreeSet<String>, state: &mut FormulaState) {
    match term.repr() {
        Forall(_, body) | Exists(_, body) => {
            let (hidden_body, patterns) = quantifier_body_and_patterns(body, user_symbols);
            state.quantifiers.push(QuantifierState {
                patterns,
                hidden_body,
            });
        }
        Annotated(inner, attrs) => {
            collect_formula_state(inner, user_symbols, state);
            for attr in attrs {
                if let Attribute::Pattern(patterns) = attr {
                    for pattern in patterns {
                        collect_visible_symbols(pattern, user_symbols, &mut state.visible_symbols);
                    }
                }
            }
        }
        Eq(left, right) => {
            collect_formula_state(left, user_symbols, state);
            collect_formula_state(right, user_symbols, state);
        }
        Distinct(items) | And(items) | Or(items) | Xor(items) => {
            for item in items {
                collect_formula_state(item, user_symbols, state);
            }
        }
        App(function, items, _) => {
            record_function_symbol(function, user_symbols, &mut state.visible_symbols);
            for item in items {
                collect_formula_state(item, user_symbols, state);
            }
        }
        Implies(left, right) => {
            for item in left {
                collect_formula_state(item, user_symbols, state);
            }
            collect_formula_state(right, user_symbols, state);
        }
        Not(inner) => collect_formula_state(inner, user_symbols, state),
        Ite(condition, then_term, else_term) => {
            collect_formula_state(condition, user_symbols, state);
            collect_formula_state(then_term, user_symbols, state);
            collect_formula_state(else_term, user_symbols, state);
        }
        Global(identifier, _) => {
            let name = identifier.id_str().get();
            if user_symbols.contains(name) {
                state.visible_symbols.insert(name.clone());
            }
        }
        Constant(..) | Local(..) => {}
        Let(..) => unreachable!("goal-distance analysis runs after let elimination"),
        Matching(..) => {}
    }
}

fn quantifier_body_and_patterns(
    body: &Term,
    user_symbols: &BTreeSet<String>,
) -> (Term, Vec<BTreeSet<String>>) {
    if let Annotated(inner, attrs) = body.repr() {
        let patterns = attrs
            .iter()
            .filter_map(|attr| match attr {
                Attribute::Pattern(terms) => Some(
                    terms
                        .iter()
                        .flat_map(|term| symbols_in_term(term, user_symbols))
                        .collect(),
                ),
                _ => None,
            })
            .collect();
        (inner.clone(), patterns)
    } else {
        (body.clone(), vec![])
    }
}

fn expand_matching_quantifiers(
    state: &mut FormulaState,
    reached_symbols: &BTreeSet<String>,
    user_symbols: &BTreeSet<String>,
) -> bool {
    let mut expanded = false;
    let mut remaining = vec![];
    let mut newly_visible = BTreeSet::new();
    let mut nested_quantifiers = vec![];

    for quantifier in state.quantifiers.drain(..) {
        if quantifier
            .patterns
            .iter()
            .any(|pattern| pattern.is_subset(reached_symbols))
        {
            let hidden_state = initialize_formula_state(&quantifier.hidden_body, user_symbols);
            newly_visible.extend(hidden_state.visible_symbols);
            nested_quantifiers.extend(hidden_state.quantifiers);
            expanded = true;
        } else {
            remaining.push(quantifier);
        }
    }

    state.visible_symbols.extend(newly_visible);
    remaining.extend(nested_quantifiers);
    state.quantifiers = remaining;
    expanded
}

fn user_defined_symbols(context: &Context) -> BTreeSet<String> {
    context
        .expose_symbol_table()
        .iter()
        .filter(|(_, entries)| entries.iter().any(|(_, meta)| !meta.is_builtin()))
        .map(|(name, _)| name.get().clone())
        .collect()
}

fn symbols_in_term(term: &Term, user_symbols: &BTreeSet<String>) -> BTreeSet<String> {
    let mut symbols = BTreeSet::new();
    collect_symbols(term, user_symbols, &mut symbols);
    symbols
}

fn collect_symbols(term: &Term, user_symbols: &BTreeSet<String>, symbols: &mut BTreeSet<String>) {
    match term.repr() {
        Annotated(inner, attrs) => {
            collect_symbols(inner, user_symbols, symbols);
            for attr in attrs {
                if let Attribute::Pattern(patterns) = attr {
                    for pattern in patterns {
                        collect_symbols(pattern, user_symbols, symbols);
                    }
                }
            }
        }
        Eq(left, right) => {
            collect_symbols(left, user_symbols, symbols);
            collect_symbols(right, user_symbols, symbols);
        }
        Distinct(items) | And(items) | Or(items) | Xor(items) => {
            for item in items {
                collect_symbols(item, user_symbols, symbols);
            }
        }
        App(function, items, _) => {
            record_function_symbol(function, user_symbols, symbols);
            for item in items {
                collect_symbols(item, user_symbols, symbols);
            }
        }
        Implies(left, right) => {
            for item in left {
                collect_symbols(item, user_symbols, symbols);
            }
            collect_symbols(right, user_symbols, symbols);
        }
        Not(inner) => collect_symbols(inner, user_symbols, symbols),
        Ite(condition, then_term, else_term) => {
            collect_symbols(condition, user_symbols, symbols);
            collect_symbols(then_term, user_symbols, symbols);
            collect_symbols(else_term, user_symbols, symbols);
        }
        Forall(_, body) | Exists(_, body) => collect_symbols(body, user_symbols, symbols),
        Global(identifier, _) => {
            let name = identifier.id_str().get();
            if user_symbols.contains(name) {
                symbols.insert(name.clone());
            }
        }
        Constant(..) | Local(..) => {}
        Let(..) => unreachable!("goal-distance analysis runs after let elimination"),
        Matching(..) => {
            // Sundance does not currently support SMT-LIB match expressions.
        }
    }
}

fn collect_visible_symbols(
    term: &Term,
    user_symbols: &BTreeSet<String>,
    symbols: &mut BTreeSet<String>,
) {
    let state = initialize_formula_state(term, user_symbols);
    symbols.extend(state.visible_symbols);
}

fn record_function_symbol(
    function: &yaspar_ir::ast::QualifiedIdentifier,
    user_symbols: &BTreeSet<String>,
    symbols: &mut BTreeSet<String>,
) {
    let name = function.id_str().get();
    if user_symbols.contains(name) {
        symbols.insert(name.clone());
    }
    if let Some(IdentifierKind::Is(constructor)) = function.get_kind() {
        let constructor = constructor.get();
        if user_symbols.contains(constructor) {
            symbols.insert(constructor.clone());
        }
    }
}

fn record_subterm_distances(
    term: &Term,
    distance: SyntacticDistance,
    distances: &mut DeterministicHashMap<u64, SyntacticDistance>,
) {
    distances
        .entry(term.uid())
        .and_modify(|old| *old = (*old).min(distance))
        .or_insert(distance);

    match term.repr() {
        Annotated(inner, attrs) => {
            record_subterm_distances(inner, distance, distances);
            for attr in attrs {
                if let Attribute::Pattern(patterns) = attr {
                    for pattern in patterns {
                        record_subterm_distances(pattern, distance, distances);
                    }
                }
            }
        }
        Eq(left, right) => {
            record_subterm_distances(left, distance, distances);
            record_subterm_distances(right, distance, distances);
        }
        Distinct(items) | And(items) | Or(items) | Xor(items) => {
            for item in items {
                record_subterm_distances(item, distance, distances);
            }
        }
        App(_, items, _) => {
            for item in items {
                record_subterm_distances(item, distance, distances);
            }
        }
        Implies(left, right) => {
            for item in left {
                record_subterm_distances(item, distance, distances);
            }
            record_subterm_distances(right, distance, distances);
        }
        Not(inner) => record_subterm_distances(inner, distance, distances),
        Ite(condition, then_term, else_term) => {
            record_subterm_distances(condition, distance, distances);
            record_subterm_distances(then_term, distance, distances);
            record_subterm_distances(else_term, distance, distances);
        }
        Forall(_, body) | Exists(_, body) => record_subterm_distances(body, distance, distances),
        Constant(..) | Global(..) | Local(..) | Let(..) | Matching(..) => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use yaspar_ir::ast::alg;
    use yaspar_ir::ast::{Context, LetElim, Repr, Typecheck};
    use yaspar_ir::untyped::UntypedAst;

    fn assertions(input: &str) -> (Context, Vec<Term>) {
        let commands = UntypedAst.parse_script_str(input).unwrap();
        let mut context = Context::new();
        let commands = commands.type_check(&mut context).unwrap();
        let assertions = commands
            .iter()
            .filter_map(|command| match command.repr() {
                alg::Command::Assert(term) => Some(term.let_elim(&mut context)),
                _ => None,
            })
            .collect();
        (context, assertions)
    }

    #[test]
    fn assertions_form_goal_relative_symbol_layers() {
        let (context, assertions) = assertions(
            r#"
            (declare-sort U 0)
            (declare-const a U)
            (declare-const b U)
            (declare-const c U)
            (declare-const d U)
            (declare-fun goal (U) Bool)
            (declare-fun near (U) U)
            (declare-fun far (U) U)
            (declare-fun unrelated (U) Bool)
            (assert (= (far b) (near c)))
            (assert (= (near c) a))
            (assert (unrelated d))
            (assert (not (goal a)))
            "#,
        );
        let distances = GoalDistance::new(&assertions, assertions.len() - 1, &context);

        assert_eq!(distances.term_distance(&assertions[3]), 0);
        assert_eq!(distances.term_distance(&assertions[1]), 1);
        assert_eq!(distances.term_distance(&assertions[0]), 2);
        assert_eq!(
            distances.term_distance(&assertions[2]),
            distances.unreachable_distance()
        );
    }

    #[test]
    fn original_subterms_inherit_their_nearest_assertion_distance() {
        let (context, assertions) = assertions(
            r#"
            (declare-sort U 0)
            (declare-const a U)
            (declare-const b U)
            (declare-fun p (U) Bool)
            (declare-fun f (U) U)
            (assert (p (f b)))
            (assert (not (p a)))
            "#,
        );
        let distances = GoalDistance::new(&assertions, 1, &context);
        let near_subterm = match assertions[0].repr() {
            App(_, args, _) => args[0].clone(),
            other => panic!("unexpected assertion: {other:?}"),
        };

        assert_eq!(distances.term_distance(&near_subterm), 1);
    }

    #[test]
    fn quantifier_body_stays_hidden_until_its_pattern_is_reachable() {
        let (context, assertions) = assertions(
            r#"
            (declare-sort U 0)
            (declare-const a U)
            (declare-const b U)
            (declare-fun goal (U) Bool)
            (declare-fun seed (U) Bool)
            (declare-fun hidden (U) Bool)
            (assert
              (forall ((x U))
                (! (=> (goal x) (hidden x))
                   :pattern ((seed x)))))
            (assert (hidden b))
            (assert (not (goal a)))
            "#,
        );
        let distances = GoalDistance::new(&assertions, 2, &context);

        assert_eq!(
            distances.term_distance(&assertions[0]),
            distances.unreachable_distance()
        );
        assert_eq!(
            distances.term_distance(&assertions[1]),
            distances.unreachable_distance()
        );
    }

    #[test]
    fn reachable_pattern_exposes_quantifier_body_in_later_rounds() {
        let (context, assertions) = assertions(
            r#"
            (declare-sort U 0)
            (declare-const a U)
            (declare-const b U)
            (declare-fun goal (U) Bool)
            (declare-fun seed (U) Bool)
            (declare-fun hidden (U) Bool)
            (assert (hidden b))
            (assert
              (forall ((x U))
                (! (hidden x)
                   :pattern ((seed x)))))
            (assert (seed a))
            (assert (not (goal a)))
            "#,
        );
        let distances = GoalDistance::new(&assertions, 3, &context);

        assert_eq!(distances.term_distance(&assertions[2]), 1);
        assert_eq!(distances.term_distance(&assertions[1]), 2);
        assert_eq!(distances.term_distance(&assertions[0]), 4);
    }
}
