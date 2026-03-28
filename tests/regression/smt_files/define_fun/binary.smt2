; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; define-fun with two parameters
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun a () T)
(declare-fun b () T)
(declare-fun h (T T) T)
(define-fun apply_h ((x T) (y T)) T (h x y))
(assert (= (apply_h a b) a))
(assert (not (= (h a b) a)))
(check-sat)
