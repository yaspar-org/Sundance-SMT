; Regression for the occurs-check tester guard.
; (tail x) = x only forms a cycle if x is a Cons. The constructor is gated
; behind Boolean b, so the model b=false, x=Nil satisfies everything and the
; occurs-check conflict clause must be guarded by (not (is-Cons x)).
(set-logic ALL)
(declare-datatypes ((IntList 0)) (((Nil) (Cons (head Int) (tail IntList)))))
(declare-const x IntList)
(declare-const b Bool)
(assert (=> b ((_ is Cons) x)))
(assert (= (tail x) x))
(check-sat)
