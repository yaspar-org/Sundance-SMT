; Test complex selector patterns and accessor chains
(declare-sort UserId 0)
(declare-sort Message 0)
(declare-datatypes ((User 0) (Channel 0) (ChatSystem 0)) (
  ((mk-user (user-id UserId) (user-name Message)))
  ((mk-channel (channel-name Message) (owner User) (member-count Int)))
  ((mk-chat (admin User) (main-channel Channel) (user-count Int)))))

(declare-const uid1 UserId)
(declare-const uid2 UserId)
(declare-const msg1 Message)
(declare-const msg2 Message)
(declare-const u1 User)
(declare-const u2 User)
(declare-const ch1 Channel)
(declare-const system ChatSystem)

; Test complex accessor chains
(assert (= system (mk-chat u1 ch1 42)))
(assert (= ch1 (mk-channel msg1 u2 10)))
(assert (= u2 (mk-user uid2 msg2)))

; Test deep accessor chains
(assert (= (user-id (owner (main-channel system))) uid2))
(assert (= (user-name (owner (main-channel system))) msg2))
(assert (= (channel-name (main-channel system)) msg1))
(assert (= (member-count (main-channel system)) 10))

; Test selector composition
(assert (= (owner (main-channel system)) u2))
(assert (= (admin system) u1))
(assert (= (user-count system) 42))

; Test that different accessor paths can refer to same objects
(assert (= u2 (owner ch1)))
(assert (= ch1 (main-channel system)))
(assert (= u2 (owner (main-channel system))))

; Test constructor-selector relationships with complex nesting
(assert (= system (mk-chat (admin system) (main-channel system) (user-count system))))
(assert (= ch1 (mk-channel (channel-name ch1) (owner ch1) (member-count ch1))))
(assert (= u2 (mk-user (user-id u2) (user-name u2))))

; Test that changing nested values changes the whole structure
(assert (not (= system (mk-chat u1 ch1 43))))
(assert (not (= system (mk-chat u2 ch1 42))))
(assert (not (= ch1 (mk-channel msg2 u2 10))))

; Test selector injectivity through complex paths
(assert (= (user-id (owner (main-channel system))) (user-id (owner ch1))))
(assert (= (user-name (owner (main-channel system))) (user-name (owner ch1))))

(check-sat)
