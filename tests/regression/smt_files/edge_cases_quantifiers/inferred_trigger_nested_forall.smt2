; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; The outer variable i occurs under an uninterpreted head only inside the
; nested forall, as (h i). Like z3, trigger inference looks inside the nested
; binder and finds (h i); (R o (h i)) mentions the nested o and is not used.
(set-logic UFLIA)
(declare-sort T 0)
(declare-fun h (Int) T)
(declare-fun R (T T) Bool)
(declare-const a T)
(assert (forall ((i Int)) (=> (<= 0 i) (forall ((o T)) (! (R o (h i)) :pattern ((R o (h i))))))))
(assert (not (R a (h 3))))
(check-sat)
