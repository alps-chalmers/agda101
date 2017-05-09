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

last-label : Statement -> Label -> Bool
last-label (composition stm1 stm2) label = last-label stm2 label
last-label (assignN (l l1) _ _) (l l2) = l1 == l2
last-label (assignB (l l1) _ _) (l l2) = l1 == l2
last-label (while (l l1) _ _) (l l2) = l1 == l2
last-label (cobegin (l l1) _ _) (l l2) = l1 == l2
verify-after-while : Statement -> Label -> Label -> Bool
verify-after-while (while (l wl) _ stm) label1 (l l2) =
  if (wl == l2) then
    (last-label stm label1)
  else
    (verify-after-while stm label1 (l l2))
verify-after-while (composition stm1 stm2) label1 label2 =
  (verify-after-while stm1 label1 label2) or
  (verify-after-while stm2 label1 label2)
verify-after-while (cobegin _ stm1 stm2) label1 label2 =
  (verify-after-while stm1 label1 label2) or
  (verify-after-while stm2 label1 label2)
verify-after-while _ _ _ = false

data Result : Set where
  valid : Result
  epic-fail : Result
  not-atomic-assignment : Label -> Result
  not-after-while : Label -> Label -> Result
  not-asr-f : Label -> BVar -> Result

_conc_ : Result -> Result -> Result
_conc_ valid x = x
_conc_ x _ = x

verify : {prog : Program} -> {prop : Props} -> prog ⊨ prop -> Result
verify (d-⊤-i _ _) = valid
verify (▢-i _ _) = valid
verify (aar (program stm) label) =
  if (verify-aar stm label) then
    valid
  else 
    (not-atomic-assignment label)
verify (d-∧-i p1 p2) = (verify p1) conc (verify p2)
verify (d-mp p1 p2) = (verify p1) conc (verify p2)
verify (assume _ _) = valid
verify (asr-f (program stm) label b) =
  if (verify-asr-f stm label b) then
    valid
  else
    (not-asr-f label b)
verify (after-while (program stm) l1 l2) =
  if (verify-after-while stm l1 l2) then
    valid
  else
    (not-after-while l1 l2)
verify _ = valid
