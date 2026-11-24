; An ill-typed command must be reported even when its frame is popped before any check.
(declare-fun p () Bool)
(push 1)
(assert undeclared)
(pop 1)
(check-sat)
