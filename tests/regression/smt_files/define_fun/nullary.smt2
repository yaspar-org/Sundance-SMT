; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; define-fun with no parameters (constant definition)
(set-logic QF_UF)
(declare-sort T 0)
(declare-fun a () T)
(declare-fun b () T)
(define-fun my_a () T a)
(assert (= my_a b))
(assert (not (= a b)))
(check-sat)
