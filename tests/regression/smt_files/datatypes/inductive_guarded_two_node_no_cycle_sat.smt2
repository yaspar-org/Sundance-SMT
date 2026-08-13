; Two-node guarded cycle: b forces is-Cons on both x and (tail x), and
; (tail (tail x)) = x would close a length-2 cycle. But b is free, so b=false
; with x=Nil is a model. Exercises a conflict clause that must negate BOTH
; testers, not just the linking equality.
(set-logic ALL)
(declare-datatypes ((IntList 0)) (((Nil) (Cons (head Int) (tail IntList)))))
(declare-const x IntList)
(declare-const b Bool)
(assert (=> b ((_ is Cons) x)))
(assert (=> b ((_ is Cons) (tail x))))
(assert (= (tail (tail x)) x))
(check-sat)
