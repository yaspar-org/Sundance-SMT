; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; define-fun with one parameter, inlined into assertion
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun a () T)
(declare-fun b () T)
(declare-fun f (T) T)
(define-fun apply_f ((x T)) T (f x))
(assert (= (apply_f a) b))
(assert (not (= (f a) b)))
(check-sat)
