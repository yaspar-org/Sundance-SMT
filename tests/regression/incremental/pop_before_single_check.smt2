; One check-sat after a pop: the popped assertion must not count.
(declare-fun p () Bool)
(push 1)
(assert (not p))
(pop 1)
(assert p)
(check-sat)
