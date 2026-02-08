; Example 
(declare-sort X 0)
(declare-datatypes ((Shape 0)) (((Circle (radius X)) (Square (side X)))))

(declare-const x X)
(declare-const y X)
(declare-const z X)


; Create contradiction: applying selector to constructor
(assert (= (radius (Circle x)) y))
(assert (not (= x y)))


(check-sat)
