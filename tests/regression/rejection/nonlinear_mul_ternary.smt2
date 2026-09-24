; Rejection test (issue #52): non-linear n-ary multiplication.
; (* x y z) has three non-constant factors, so it cannot be linearized. The
; internal arithmetic solver must reject this rather than silently dropping the
; extra factors (the old binary-only `*` handling left (* a b c) collapsing to
; 0, which would make this look unsat via 0 = 8; the real answer is sat, e.g.
; x = y = 2, z = 2).
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= (* x y z) 8))
(check-sat)
