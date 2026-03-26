; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; define-fun returning Bool used in assertion
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun a () T)
(declare-fun b () T)
(define-fun eq_ab ((x T) (y T)) Bool (= x y))
(assert (eq_ab a b))
(assert (not (= a b)))
(check-sat)
