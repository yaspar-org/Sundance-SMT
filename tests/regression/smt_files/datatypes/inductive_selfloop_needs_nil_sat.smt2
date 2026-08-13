; (tail x) = x is satisfiable by choosing x = Nil (so tail x is unconstrained
; and can equal x). The solver must NOT learn an unconditional (tail x) != x.
(set-logic ALL)
(declare-datatypes ((IntList 0)) (((Nil) (Cons (head Int) (tail IntList)))))
(declare-const x IntList)
(assert (= (tail x) x))
(check-sat)
