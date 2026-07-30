// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use sundance_smt::egraphs::{Egraph, EgraphTrait, Op};

fn term(egraph: &mut Egraph, op: &str, children: &[u32]) -> u32 {
    egraph.register_term(Op::App(op.to_string()), children, false)
}

#[test]
fn registration_congruence_is_deferred_until_rebuild() {
    let mut egraph = Egraph::new();
    let a = term(&mut egraph, "a", &[]);
    let first = term(&mut egraph, "f", &[a]);
    let second = term(&mut egraph, "f", &[a]);

    assert!(!egraph.are_equal(first, second));
    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.are_equal(first, second));
}

#[test]
fn dynamic_registration_congruence_is_deferred_until_rebuild() {
    let mut egraph = Egraph::new();
    let a = term(&mut egraph, "a", &[]);
    let b = term(&mut egraph, "b", &[]);
    let first = term(&mut egraph, "f", &[a]);

    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.assert_equal(a, b).conflict.is_none());
    assert!(egraph.rebuild().conflict.is_none());

    let second = egraph.register_term(Op::App("f".to_string()), &[b], true);
    assert!(!egraph.are_equal(first, second));

    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.are_equal(first, second));
}

#[test]
fn rebuild_computes_congruence_to_a_fixed_point() {
    let mut egraph = Egraph::new();
    let a = term(&mut egraph, "a", &[]);
    let b = term(&mut egraph, "b", &[]);
    let f_a = term(&mut egraph, "f", &[a]);
    let f_b = term(&mut egraph, "f", &[b]);
    let g_f_a = term(&mut egraph, "g", &[f_a]);
    let g_f_b = term(&mut egraph, "g", &[f_b]);

    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.assert_equal(a, b).conflict.is_none());
    assert!(!egraph.are_equal(f_a, f_b));
    assert!(!egraph.are_equal(g_f_a, g_f_b));

    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.are_equal(f_a, f_b));
    assert!(egraph.are_equal(g_f_a, g_f_b));
}

#[test]
fn rebuild_reports_conflicts_from_deferred_congruence() {
    let mut egraph = Egraph::new();
    let a = term(&mut egraph, "a", &[]);
    let b = term(&mut egraph, "b", &[]);
    let f_a = term(&mut egraph, "f", &[a]);
    let f_b = term(&mut egraph, "f", &[b]);

    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.assert_disequal(f_a, f_b, 7).conflict.is_none());
    assert!(egraph.assert_equal(a, b).conflict.is_none());
    assert!(!egraph.are_equal(f_a, f_b));

    let conflict = egraph
        .rebuild()
        .conflict
        .expect("deferred congruence must violate the asserted disequality");
    assert_eq!(conflict.diseq_lit, Some(7));
}

#[test]
fn backtracking_rebuilds_signatures_at_the_restored_level() {
    let mut egraph = Egraph::new();
    let a = term(&mut egraph, "a", &[]);
    let b = term(&mut egraph, "b", &[]);
    let f_a = term(&mut egraph, "f", &[a]);
    let f_b = term(&mut egraph, "f", &[b]);

    assert!(egraph.rebuild().conflict.is_none());
    egraph.notify_new_decision_level();
    assert!(egraph.assert_equal(a, b).conflict.is_none());
    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.are_equal(f_a, f_b));

    egraph.backtrack_to(0);
    assert!(!egraph.are_equal(a, b));
    assert!(!egraph.are_equal(f_a, f_b));
    assert!(egraph.rebuild().conflict.is_none());
    assert!(!egraph.are_equal(f_a, f_b));
}
