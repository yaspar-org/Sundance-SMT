; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; No single candidate covers {x, y}; the candidates are (g x), (h y) and (k x).
; Like z3, the multi-pattern takes them in order, so it is {(g x), (h y)}. There
; is no k-term, so {(k x), (h y)} would never produce x := a, y := b.
(set-logic UFLIA)
(declare-sort T 0)
(declare-fun g (T) Int)
(declare-fun h (T) Int)
(declare-fun k (T) Int)
(declare-const a T)
(declare-const b T)
(assert (forall ((x T) (y T)) (= (+ (g x) (h y) (* 0 (k x))) 0)))
(assert (= (g a) 1))
(assert (= (h b) 1))
(check-sat)
