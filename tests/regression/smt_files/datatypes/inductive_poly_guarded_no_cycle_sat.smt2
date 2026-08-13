; Polymorphic list version of the guarded self-loop: (tail x) = x with no
; forced constructor. Satisfiable with x = Nil. Exercises the tester guard on a
; monomorphized (List Int) sort.
(set-logic ALL)
(declare-datatypes ((List 1)) ((par (T) ((Nil) (Cons (head T) (tail (List T)))))))
(declare-const x (List Int))
(assert (= (tail x) x))
(check-sat)
