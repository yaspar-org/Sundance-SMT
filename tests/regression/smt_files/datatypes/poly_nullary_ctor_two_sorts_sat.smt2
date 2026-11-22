; None at (Option Int) and None at (Option Bool) are distinct terms of distinct sorts;
; val is unconstrained on None, so (val x) = 5 and (val y) = true are both satisfiable.
(declare-datatypes ((Option 1)) ((par (T) ((None) (Some (val T))))))

(declare-const x (Option Int))
(declare-const y (Option Bool))

(assert ((_ is None) x))
(assert ((_ is None) y))
(assert (= (val x) 5))
(assert (val y))

(check-sat)
