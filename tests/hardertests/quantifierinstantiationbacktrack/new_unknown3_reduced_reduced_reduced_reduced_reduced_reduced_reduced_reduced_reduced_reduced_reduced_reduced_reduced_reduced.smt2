(declare-sort P 0)
; note if we solve all instances of Int 
; I think this is something to do with how Int and quantifier instantiation interact
; actually if we turn off nelson-oppen this is solvable
(declare-fun I (Int) P)
(declare-fun h (P) Bool)
(declare-fun i (P) P)
(declare-fun b (P) P)
(declare-fun b1 (P) Int)
(declare-fun P (P) P)
(declare-fun v (P) P)
(declare-fun v2 (P) P)
(declare-fun l (P P) P)
(declare-const zero Int)
(assert (forall ((r P)) (! (h (P (i r))) :pattern ((i r)))))
(assert (forall ((t P) (e P)) (! (= (v t) (l t e)) :pattern ((l t e)))))
(assert (not (h (v (I zero)))))
(assert (= (I zero) (i (I zero))))
(assert (= (I zero) (l (I zero) (I (b1 (I zero))))))
(assert (= (I zero) (P (I zero))))
(assert (= (v (I zero)) (i (l (I zero) (I (b1 (v2 (I zero))))))))

   ; can discover these instantiations and concluded unsat from them, but not enough to do both steps idk why
   ;(assert (h (P (i (I zero)))))
   ;(assert (= (v (I zero)) (l (I zero) (I (b1 (I zero))))))

(check-sat)
