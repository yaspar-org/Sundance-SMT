(declare-sort S 0)
(declare-fun f (S) Bool)

(assert (exists ((t S)) (! (and (not (f t)) (forall ((s S)) (! (and (f t) (f s)) :pattern ((f s))))) :pattern ((f t)))))
(check-sat)