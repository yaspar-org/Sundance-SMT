; Rejection test: fixed-size bitvectors are an unsupported theory.
; Verus VC benchmark (solver flavor: cvc5), expected unsat (Verus proved this VC).
; Every bitvector operator here (bvor, bvshl, bvand, extract, zero_extend) used to be
; registered as an uninterpreted function, so congruence closure alone constrained it and
; the solver reported `sat` for this unsat problem. Sundance must reject the input instead.
(declare-sort %%Function%% 0)
(declare-const prefix! (_ BitVec 64))
(declare-const low_word! (_ BitVec 64))
(assert
 true
)
(declare-const %%location_label%%0 Bool)
(assert
 (not (=>
   %%location_label%%0
   (= ((_ extract 31 0) (bvor (bvshl prefix! ((_ zero_extend 58) (_ bv32 6))) (bvand low_word!
       ((_ zero_extend 32) (_ bv4294967295 32))
     ))
    ) ((_ extract 31 0) low_word!)
))))
(check-sat)
