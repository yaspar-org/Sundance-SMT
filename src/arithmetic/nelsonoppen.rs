// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::egraphs::egraph::Egraph;
use yaspar_ir::ast::ATerm::*;
use yaspar_ir::ast::FetchSort;
use yaspar_ir::ast::{
    alg::QualifiedIdentifier, ObjectAllocatorExt as _, Repr, StrAllocator, Term, TermAllocator,
};

pub fn nelson_oppen_clause(literal: i32, egraph: &mut Egraph) -> Option<Term> {
    let term = egraph.get_term_from_lit(-literal);
    match term.repr() {
        Eq(x, y) => {
            if x.get_sort(&mut egraph.context).to_string() == "Int"
                && y.get_sort(&mut egraph.context).to_string() == "Int"
            {
                let bool_sort = egraph.context.bool_sort();

                let lt = QualifiedIdentifier::simple(egraph.context.allocate_symbol("<"));
                let lt_term =
                    egraph
                        .context
                        .app(lt, vec![x.clone(), y.clone()], Some(bool_sort.clone()));

                let gt = QualifiedIdentifier::simple(egraph.context.allocate_symbol(">"));
                let gt_term = egraph
                    .context
                    .app(gt, vec![x.clone(), y.clone()], Some(bool_sort));

                let or = egraph.context.or(vec![lt_term, gt_term, term]);

                Some(or)
            } else {
                None
            }
        }
        _ => None,
    }
}

// pub fn nelson_oppen_clause_ineq(literal: i32, egraph: &mut Egraph) -> Option<Term> {
//     let term = egraph.get_term_from_lit(-literal);
//     // todo: sometimes literal can be in wrong polarity not sure why, but need to fix this
//     let term_positive = if let Not(t) = term.repr() {t.clone()} else {term};
//     match term_positive.repr() {
//         App(f, terms, _) => {
//             let f = f.to_string();
//             assert!(f == "<" || f == ">" || f == ">=" || f == "<=");
//             assert!(terms.len() == 2);
//             let (x, y) = (&terms[0], &terms[1]);

//             if egraph.nelson_oppen_ineq_literals.contains(&(x.uid(), y.uid())) {
//                 return None
//             }
//             egraph.nelson_oppen_ineq_literals.insert((x.uid(), y.uid()));

//             let bool_sort = egraph.context.bool_sort();

//             let lt = QualifiedIdentifier::simple(egraph.context.allocate_symbol("<"));
//             let lt_term = egraph.context.app(lt, vec![x.clone(), y.clone()], Some(bool_sort.clone()));

//             let gt = QualifiedIdentifier::simple(egraph.context.allocate_symbol(">"));
//             let gt_term = egraph.context.app(gt, vec![x.clone(), y.clone()], Some(bool_sort));

//             let eq_term = egraph.context.eq(x.clone(), y.clone());

//             let or = egraph.context.or(vec![lt_term, gt_term, eq_term]);

//             // println!("(assert {or}) with lit {literal} and term {term_positive}");

//             Some(or)

//         },
//         _ => {
//             panic!("{} should be an inequality", term_positive);
//         }
//     }
// }

// learn the clause x = y \/ x > y \/ x < y
pub fn nelson_oppen_clause_pair(x: u64, y: u64, egraph: &mut Egraph) -> Option<Term> {
    if egraph.nelson_oppen_ineq_literals.contains(&(x, y)) {
        return None;
    }
    egraph.nelson_oppen_ineq_literals.insert((x, y));

    let bool_sort = egraph.context.bool_sort();

    let lt = QualifiedIdentifier::simple(egraph.context.allocate_symbol("<"));
    let lt_term = egraph.context.app(
        lt,
        vec![egraph.get_term(x), egraph.get_term(y)],
        Some(bool_sort.clone()),
    );

    let gt = QualifiedIdentifier::simple(egraph.context.allocate_symbol(">"));
    let gt_term = egraph.context.app(
        gt,
        vec![egraph.get_term(x), egraph.get_term(y)],
        Some(bool_sort),
    );

    let eq_term = egraph.context.eq(egraph.get_term(x), egraph.get_term(y));

    let or = egraph.context.or(vec![lt_term, gt_term, eq_term]);

    Some(or)
}
