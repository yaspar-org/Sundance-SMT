; Two Boolean terms share a literal (one is the NNF of the other); both need its truth value in the e-graph. Issue #262.
(set-logic QF_UF)
(declare-fun f (Bool) Bool)
(declare-const a Bool)
(assert (not (= (f a) (f (not (not a))))))
(check-sat)
