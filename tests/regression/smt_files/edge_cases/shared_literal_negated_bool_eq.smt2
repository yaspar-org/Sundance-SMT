; The ite condition shares a literal with its NNF and used to hit assert!(sign) when assigned false. Issue #264.
(set-logic QF_UFLIA)
(declare-const p Bool)
(declare-const q Bool)
(declare-const z Int)
(assert (= p q))
(assert (= z (ite (not (= p q)) 1 2)))
(check-sat)
