; Mixed sum-product type - variants with different field structures
(declare-sort Name 0)
(declare-sort Address 0)
(declare-datatypes ((Contact 0)) (
  ((Phone (number Int))
   (Email (addr Address)) 
   (InPerson (name Name) (location Address)))))

(declare-const n1 Name)
(declare-const addr1 Address)
(declare-const addr2 Address)
(declare-const contact1 Contact)
(declare-const contact2 Contact)

; Test constructor recognizers for each variant
(assert ((_ is Phone) (Phone 5551234)))
(assert ((_ is Email) (Email addr1)))
(assert ((_ is InPerson) (InPerson n1 addr1)))

; Test constructor distinctness
(assert (not (= (Phone 5551234) (Email addr1))))
(assert (not (= (Phone 5551234) (InPerson n1 addr1))))
(assert (not (= (Email addr1) (InPerson n1 addr1))))

; Test selectors for each variant
(assert (= (number (Phone 5551234)) 5551234))
(assert (= (addr (Email addr1)) addr1))
(assert (= (name (InPerson n1 addr1)) n1))
(assert (= (location (InPerson n1 addr1)) addr1))

; Test constructor injectivity within variants
(assert (not (= (Phone 5551234) (Phone 5559876))))
(assert (not (= (Email addr1) (Email addr2))))
(assert (not (= (InPerson n1 addr1) (InPerson n1 addr2))))

; Test selector-constructor relationship
(assert ((_ is Phone) contact1))
(assert (= contact1 (Phone (number contact1))))

; Test with mixed constraints
(assert ((_ is InPerson) contact2))
(assert (= (name contact2) n1))
(assert (not ((_ is Phone) contact2)))
(assert (not ((_ is Email) contact2)))

(check-sat)
