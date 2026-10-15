; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0

; The only candidate, (le 0 l), is listed in :no-pattern. z3 then ignores the
; annotation ("ignoring nopats annotation because Z3 couldn't find any other
; pattern") and uses it, which gives the instance l := 5.
(set-logic UFLIA)
(declare-fun le (Int Int) Bool)
(declare-const c Bool)
(assert (forall ((l Int)) (! (=> (le 0 l) c) :no-pattern (le 0 l))))
(assert (le 0 5))
(assert (not c))
(check-sat)
