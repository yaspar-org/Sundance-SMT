// helper functions for the egraph and congruence closure

use yaspar_ir::ast::ATerm::*;
use yaspar_ir::ast::Attribute;
use yaspar_ir::ast::Repr;
use yaspar_ir::ast::Term;

// a helper function to get subterms of a Term
pub fn get_subterms(term: &Term) -> (String, Vec<&Term>) {
    match term.repr() {
        Annotated(term, _) => {
            let (func, mut subterms) = get_subterms(term);
            debug_println!(
                6,
                0,
                "We are adding the subterm of a annotated term {:?}",
                subterms
            );
            subterms.push(term);
            (func, subterms)
        }
        Eq(left, right) => ("=".to_string(), vec![left, right]),
        Distinct(items) => ("distinct".to_string(), items.iter().collect()),
        And(items) => ("and".to_string(), items.iter().collect()),
        Or(items) => ("or".to_string(), items.iter().collect()),
        App(func, items, _) => {
            debug_println!(10, 0, "We have the func {:?}", func);
            let func_indices = &func.0.indices;
            let func_id = func.id_str();
            if func_indices.is_empty() {
                (func_id.get().clone(), items.iter().collect())
            } else {
                assert_eq!(*func_id.get(), "is".to_string());
                assert_eq!(func_indices.len(), 1);
                let r = format!("(is {})", func_indices[0].clone());
                (r, items.iter().collect())
            }
        }
        Implies(left, right) => {
            let mut subterms: Vec<&Term> = left.iter().collect();
            subterms.push(right);
            ("=>".to_string(), subterms)
        }
        Not(t) => ("not".to_string(), vec![t]),
        // might want b last because in the quantifier case, need to introduce t1, t2 before we do a union_predecessors on b
        // but switched it back because we changed how we did union_process_ite
        Ite(b, t1, t2) => ("ite".to_string(), vec![b, t1, t2]),
        Let(_, _) => panic!("We should have inlined all Let bindings"),
        // TODO: not activating quantifiers for right now
        Matching(..) => todo!(),
        Forall(_, middle_term) | Exists(_, middle_term) => {
            if let Annotated(inner_term, attrs) = middle_term.repr() {
                let mut subterms = vec![inner_term];
                for attr in attrs.iter() {
                    if let Attribute::Pattern(s_exprs) = &attr {
                        subterms.extend(s_exprs.iter());
                    }
                }
                let name = if let Forall(..) = term.repr() {
                    "forall".to_string()
                } else {
                    "exists".to_string()
                };
                (name, subterms)
            } else {
                panic!("We have a forall/exists case that is not annotated");
            }
        }
        Constant(..) | Global(..) | Local(..) => ("".to_string(), vec![]), // else case for constant, global, local
    }
}
