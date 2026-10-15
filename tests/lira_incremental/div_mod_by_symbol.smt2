; div/mod whose divisor is a symbol, not a numeral. The incremental internal backend used to
; abort on these (`register_var failed: div/mod divisor VarId N is not a constant`). It now treats
; such terms as opaque integers; unsat follows from the disjunction alone.
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (> y 0))
(assert (or (= (div x y) 1) (= (div x y) 2)))
(assert (< (div x y) 1))
(assert (>= (mod x y) 0))
(check-sat)
