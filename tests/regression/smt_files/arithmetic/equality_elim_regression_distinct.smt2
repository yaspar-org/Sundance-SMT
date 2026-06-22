; Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
; SPDX-License-Identifier: Apache-2.0
 
(declare-fun n () Int)
(assert (= 5 (+ n 1)))
(assert (distinct n 4))
(check-sat)
