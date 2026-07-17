// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use sundance_smt::egraphs::{Egraph, EgraphTrait, Op, Pattern};

#[test]
fn ematch_reports_concrete_roots_for_nested_multipatterns() {
    let mut egraph = Egraph::new();
    let a = egraph.register_term(Op::App("a".to_string()), &[], false);
    let b = egraph.register_term(Op::App("b".to_string()), &[], false);
    let g_a = egraph.register_term(Op::App("g".to_string()), &[a], false);
    let g_b = egraph.register_term(Op::App("g".to_string()), &[b], false);
    let f_g_a = egraph.register_term(Op::App("f".to_string()), &[g_a], false);
    let _f_g_b = egraph.register_term(Op::App("f".to_string()), &[g_b], false);
    let h_a = egraph.register_term(Op::App("h".to_string()), &[a], false);

    let f_pattern = egraph.compile_pattern(Pattern::App(
        Op::App("f".to_string()),
        vec![Pattern::App(
            Op::App("g".to_string()),
            vec![Pattern::Var("x".to_string())],
        )],
    ));
    let h_pattern = egraph.compile_pattern(Pattern::App(
        Op::App("h".to_string()),
        vec![Pattern::Var("x".to_string())],
    ));

    let matches = egraph.match_triggers(vec![(f_pattern, None), (h_pattern, None)]);

    assert_eq!(matches.len(), 1);
    assert_eq!(matches[0].substitution.get("x"), Some(&a));
    assert_eq!(matches[0].matched_terms, vec![f_g_a, h_a]);
}
