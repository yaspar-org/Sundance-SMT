; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

(set-logic QF_UFLIA)
; x <= y <= x forces x = y, so (g x) = (g y) by congruence.
(declare-fun g (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (<= x y))
(assert (<= y x))
(assert (< (g x) (g y)))
(check-sat)
