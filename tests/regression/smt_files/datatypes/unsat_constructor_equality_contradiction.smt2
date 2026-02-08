; Test unsatisfiable constructor equality contradictions
(declare-sort X 0)
(declare-datatypes ((Shape 0)) (((Circle (radius X)) (Square (side X)))))

(declare-const x X)
(declare-const y X)

; Create contradiction: same constructor but different field values
(assert (= (Circle x) (Circle y)))
(assert (not (= x y)))
;(assert (= (radius (Circle x)) x))
;(assert (= (radius (Circle y)) y))

(check-sat)
