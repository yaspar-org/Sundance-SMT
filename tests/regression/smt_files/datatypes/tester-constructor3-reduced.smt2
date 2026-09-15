; Reduced from tester-constructor3.smt2 via ddsmt.
; Requires classify_recursive to recursively classify Boolean sub-terms
; of App arguments. Without that, (or (= s (P se))) inside (B (or ...))
; never gets an Or(1) NodeKind, and lit for (= s (P se)) never becomes
; relevant when SAT decides it. The theory then misses the constructor
; conflict (s = P(se) combined with se = P(se) forces s = se).
(declare-const x Bool)
(declare-sort P 0)
(declare-fun B (Bool) Bool)
(declare-fun % (P) Bool)
(assert (forall ((x Bool)) (! x :pattern ((B x)))))
(declare-datatypes ((s 0)) (((s) (se))))
(declare-fun P (s) s)
(declare-fun %P (P) s)
(assert (= se (P se)))
(assert (B (or (= s (P se)))))
(check-sat)
