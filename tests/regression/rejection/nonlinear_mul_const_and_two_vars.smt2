; Rejection test (issue #52): non-linear n-ary multiplication with a constant
; factor. (* 2 x y) folds the leading constant (2 * x) but still leaves two
; non-constant factors (2x) * y, which is non-linear. The internal arithmetic
; solver must reject this rather than silently collapsing to 0 (which would
; make this look unsat via 0 = 8; the real answer is sat, e.g. x = 2, y = 2).
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (= (* 2 x y) 8))
(check-sat)
