; Forced into recursive path but satisfiable: x must be ctorA_rec,
; but its B-child can be ctorB_safe, breaking the chain.
(set-logic ALL)
(declare-datatypes ((A 0) (B 0) (D 0))
  (((ctorA_rec (selAr B)) (ctorA_safe (selAs D)))
   ((ctorB_rec (selBr A)) (ctorB_safe (selBs D)))
   ((ctorD_val (selD Int)))))
(declare-const x A)
(assert (not ((_ is ctorA_safe) x)))
(check-sat)
