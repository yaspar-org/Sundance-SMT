; The (non-incremental) internal arithmetic backend does not support Real; only
; internalincremental and z3incremental do.
(set-logic QF_LRA)
(declare-const x Real)
(assert (< 0 x))
(assert (< x 1))
(check-sat)
