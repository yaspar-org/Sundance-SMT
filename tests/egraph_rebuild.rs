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
fn adaptive_full_rebuild_merges_registered_congruences() {
    let mut egraph = Egraph::new();
    let mut duplicate_pairs = Vec::new();

    for i in 0..600 {
        term(&mut egraph, &format!("seed{i}"), &[]);
    }
    assert!(egraph.rebuild().conflict.is_none());

    for i in 0..400 {
        let child = term(&mut egraph, &format!("a{i}"), &[]);
        let first = term(&mut egraph, "f", &[child]);
        let second = term(&mut egraph, "f", &[child]);
        duplicate_pairs.push((first, second));
    }

    assert!(egraph.rebuild().conflict.is_none());
    assert!(
        duplicate_pairs
            .into_iter()
            .all(|(first, second)| egraph.are_equal(first, second))
    );
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

#[test]
fn backtracking_discards_abandoned_pending_congruence() {
    let mut egraph = Egraph::new();
    let a = term(&mut egraph, "a", &[]);
    let b = term(&mut egraph, "b", &[]);
    let f_a = term(&mut egraph, "f", &[a]);
    let f_b = term(&mut egraph, "f", &[b]);

    assert!(egraph.rebuild().conflict.is_none());
    egraph.notify_new_decision_level();
    assert!(egraph.assert_equal(a, b).conflict.is_none());
    egraph.backtrack_to(0);

    assert!(egraph.rebuild().conflict.is_none());
    assert!(!egraph.are_equal(a, b));
    assert!(!egraph.are_equal(f_a, f_b));
}

#[test]
fn backtracking_restores_signature_cache_to_intermediate_level() {
    let mut egraph = Egraph::new();
    let a = term(&mut egraph, "a", &[]);
    let b = term(&mut egraph, "b", &[]);
    let c = term(&mut egraph, "c", &[]);
    let f_a = term(&mut egraph, "f", &[a]);
    let f_b = term(&mut egraph, "f", &[b]);
    let f_c = term(&mut egraph, "f", &[c]);

    assert!(egraph.rebuild().conflict.is_none());
    egraph.notify_new_decision_level();
    assert!(egraph.assert_equal(a, b).conflict.is_none());
    assert!(egraph.rebuild().conflict.is_none());

    egraph.notify_new_decision_level();
    assert!(egraph.assert_equal(b, c).conflict.is_none());
    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.are_equal(f_a, f_c));

    egraph.backtrack_to(1);
    assert!(egraph.are_equal(f_a, f_b));
    assert!(!egraph.are_equal(f_a, f_c));
    assert!(egraph.rebuild().conflict.is_none());
    assert!(!egraph.are_equal(f_a, f_c));

    egraph.backtrack_to(0);
    assert!(!egraph.are_equal(f_a, f_b));
    assert!(egraph.rebuild().conflict.is_none());
    assert!(!egraph.are_equal(f_a, f_b));
}

#[test]
fn backtracking_replays_persistent_dynamic_registration() {
    let mut egraph = Egraph::new();
    let a = term(&mut egraph, "a", &[]);
    let first = term(&mut egraph, "f", &[a]);

    assert!(egraph.rebuild().conflict.is_none());
    egraph.notify_new_decision_level();
    let second = egraph.register_term(Op::App("f".to_string()), &[a], true);
    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.are_equal(first, second));

    egraph.backtrack_to(0);
    assert!(!egraph.are_equal(first, second));
    assert!(egraph.rebuild().conflict.is_none());
    assert!(egraph.are_equal(first, second));
}
