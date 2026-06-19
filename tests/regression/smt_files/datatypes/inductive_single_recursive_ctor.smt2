(set-logic ALL)
; Only one constructor (recursive) plus a base
(declare-datatypes ((S 0)) (((base) (wrap (inner S)))))
(declare-const s S)
(assert ((_ is wrap) s))
(assert (= (inner s) s))
(check-sat)
