module Veryfire where


open import LTL
open import Statement
open import Label
open import Bool
open import N
open import Props

-- verify that a certain statement is an atomic aśsignment
verify-aar : Statement -> Label -> Bool
verify-aar (assignN (l l1) _ _) (l l2) = l1 == l2
verify-aar (assignB (l l1) _ _) (l l2) = l1 == l2
verify-aar (composition stm1 stm2) label = (verify-aar stm1 label) or
                                           (verify-aar stm2 label)
verify-aar (while _ _ stm) label = verify-aar stm label
verify-aar (cobegin _ stm1 stm2) label = (verify-aar stm1 label) or
                                         (verify-aar stm2 label)

verify-asr-f : Statement -> Label -> BVar -> Bool
verify-asr-f (assignN _ _ _) _ _ = false
verify-asr-f (assignB (l l1) (bvar b1) (constB false)) (l l2) (bvar b2) =
  (l1 == l2) and (b1 == b2)
verify-asr-f (assignB (l l1) (bvar b1) _) (l l2) (bvar b2) = false
verify-asr-f (composition stm1 stm2) label b = (verify-asr-f stm1 label b) or
                                               (verify-asr-f stm2 label b)
verify-asr-f (while _ _ stm) label b = (verify-asr-f stm label b)
verify-asr-f (cobegin _ stm1 stm2) label b = (verify-asr-f stm1 label b) or
                                           (verify-asr-f stm2 label b)

verify : {prog : Program} -> {prop : Props} -> prog ⊨ prop -> Bool
verify (d-⊤-i _ _) = true
verify (▢-i _ _) = true
verify (aar (program stm) label) = verify-aar stm label
verify (d-∧-i p1 p2) = (verify p1) and (verify p2)
verify (d-mp p1 p2) = (verify p1) and (verify p2)
verify (assume _ _) = true
verify (asr-f (program stm) label b) = verify-asr-f stm label b
verify _ = true
