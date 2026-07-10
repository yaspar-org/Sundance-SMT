; Stress test for incremental Z3 with big-integer constants (2^64-scale) combined with
; egraph congruence. Analog of the atmosphere_reduced pattern:
; uHi(SZ) via SZ==64 congruence, uHi(64)==2^64 constraint, x==uHi(SZ)-1,
; and a contradictory x==0.
(set-logic QF_UFLIA)
(declare-fun SZ () Int)
(declare-fun uHi (Int) Int)
(declare-fun x () Int)
(assert (= SZ 64))
(assert (= (uHi 64) 18446744073709551616))
(assert (= x (- (uHi SZ) 1)))
(assert (= x 0))
(check-sat)
