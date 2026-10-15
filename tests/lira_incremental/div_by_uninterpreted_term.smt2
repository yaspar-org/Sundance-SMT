; The divisor is an uninterpreted constant that is only equal to a numeral through an assertion,
; like Verus' `PTE_SIZE_SPEC` or Dafny's `NodeBlockSizeUint64`. The incremental internal backend
; used to abort here; it now treats the div/mod terms as opaque and finds the conflict through
; the egraph.
(set-logic ALL)
(declare-fun size () Int)
(declare-fun f (Int) Int)
(declare-const x Int)
(assert (= size 4096))
(assert (= (f (div x size)) 3))
(assert (= (f (mod x size)) 4))
(assert (= (div x size) (mod x size)))
(check-sat)
