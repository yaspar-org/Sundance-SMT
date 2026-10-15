; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

(set-logic QF_UFLIA)
; s = n + 1 = 6 = t, so congruence gives (len s) = (len t). Only arithmetic knows s = t.
(declare-fun len (Int) Int)
(declare-const s Int)
(declare-const t Int)
(declare-const n Int)
(assert (= n 5))
(assert (= s (+ n 1)))
(assert (= t 6))
(assert (< (len s) (len t)))
(check-sat)
