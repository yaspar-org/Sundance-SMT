(declare-sort P 0)
(declare-datatypes ((o 0) (i 0) (l 0)) (((i (li P))) ((L (I P))) ((R) (T))))
(declare-fun l (l) P)
(declare-fun o (i) P)
(declare-fun PolyRT. (l) P)
(declare-fun %PolyRT. (P) l)
(assert (forall ((x l)) (! (= x (%PolyRT. (PolyRT. x))) :pattern ((l x)))))
(declare-const input! P)
; note that commenting this in make sundance unknown (even with quantifier) even though this in the only QI
;(assert (= (%PolyRT. input!) (%PolyRT. (PolyRT. (%PolyRT. input!)))))
(assert (= input! (PolyRT. (%PolyRT. input!))))
(assert (= (l (%PolyRT. input!)) (l (%PolyRT. input!))))

; seems like these three result in things being assigned but idk why
;(assert (or (not ((_ is T) T)) (not ((_ is R) T))))
;(assert (or (not ((_ is T) (%PolyRT. input!))) (not ((_ is R) (%PolyRT. input!)))))
;(assert (or (not ((_ is T) (%PolyRT. (PolyRT. (%PolyRT. input!))))) (not ((_ is R) (%PolyRT. (PolyRT. (%PolyRT. input!)))))))


; the weird thing is that when you add 2, 3, or 5, Sundance cannot solve the thing anymore
;(assert (or ((_ is R) (%PolyRT. input!)) ((_ is T) (%PolyRT. input!))))
;(assert (or ((_ is R) (%PolyRT. (PolyRT. (%PolyRT. input!)))) ((_ is T) (%PolyRT. (PolyRT. (%PolyRT. input!))))))
;(assert (=> ((_ is T) (%PolyRT. (PolyRT. (%PolyRT. input!)))) (= (%PolyRT. (PolyRT. (%PolyRT. input!))) T)))
;(assert (=> ((_ is T) (%PolyRT. input!)) (= (%PolyRT. input!) T)))
;(assert (= (%PolyRT. input!) (%PolyRT. (PolyRT. (%PolyRT. input!)))))
(check-sat)
