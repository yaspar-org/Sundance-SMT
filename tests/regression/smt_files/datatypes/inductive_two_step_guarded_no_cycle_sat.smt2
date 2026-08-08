; Two-step potential cycle x -> (tail x) -> (tail (tail x)) closed by
; (tail (tail x)) = x. It is only a real cycle if both x and (tail x) are Cons.
; Nothing forces either tester, so x = Nil (hence tail x, tail (tail x)
; unconstrained and all equal to x) satisfies it. Guards on both testers needed.
(set-logic ALL)
(declare-datatypes ((IntList 0)) (((Nil) (Cons (head Int) (tail IntList)))))
(declare-const x IntList)
(assert (= (tail (tail x)) x))
(check-sat)
