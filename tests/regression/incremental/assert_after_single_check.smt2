; One check-sat: assertions after it (or after exit) are not in scope at the check.
(declare-fun p () Bool)
(assert p)
(check-sat)
(assert (not p))
(exit)
(assert (not p))
