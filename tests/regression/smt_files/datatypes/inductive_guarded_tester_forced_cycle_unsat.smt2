; Companion to inductive_guarded_tester_no_cycle_sat: here b is forced true,
; so (is-Cons x) holds, x = Cons(head x, tail x), and (tail x) = x makes x a
; subterm of itself. Unsat by the occurs check.
(set-logic ALL)
(declare-datatypes ((IntList 0)) (((Nil) (Cons (head Int) (tail IntList)))))
(declare-const x IntList)
(declare-const b Bool)
(assert b)
(assert (=> b ((_ is Cons) x)))
(assert (= (tail x) x))
(check-sat)
