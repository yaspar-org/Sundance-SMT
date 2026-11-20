; Two Boolean terms share a literal (one is the NNF of the other); both need its truth value in the e-graph. Issue #262.
(set-logic QF_UF)
(declare-fun f (Bool) Bool)
(declare-const a Bool)
(declare-const b Bool)
(assert (not (= (f (=> a b)) (f (or (not a) b)))))
(check-sat)
