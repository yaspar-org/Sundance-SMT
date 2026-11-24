; Boogie/Dafny style: push, assertions, one check-sat (solved as a single query).
(declare-fun p () Bool)
(push 1)
(assert p)
(assert (not p))
(check-sat)
(pop 1)
