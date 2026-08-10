; The self-loop (tail x) = x is asserted, and separately (is-Cons x OR p).
; Satisfiable by p=true, x=Nil: the disjunction is met without forcing is-Cons,
; so no cycle. Confirms the guarded occurs-check clause lets the SAT solver keep
; x = Nil available.
(set-logic ALL)
(declare-datatypes ((IntList 0)) (((Nil) (Cons (head Int) (tail IntList)))))
(declare-const x IntList)
(declare-const p Bool)
(assert (or ((_ is Cons) x) p))
(assert (= (tail x) x))
(check-sat)
