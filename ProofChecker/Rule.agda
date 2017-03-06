module Rule where

open import LTL
open import Nat
open import LTLRules
open import Lists

record Rule : Set1 where
  constructor rule
  field stm   : LTL -- Hoare Triple
        r     : LTL -> LTL


^-e1 : LTL -> LTL
^-e1 (φ ∧ _) = φ
^-e1 _ = ⊥

tRule : Rule
tRule = rule (T ∧ ⊥) ^-e1

test : LTL
test = (Rule.r tRule) (Rule.stm tRule)

testSeq : {n : Nat} {σ : Seq n} {φ ψ : LTL} -> σ ⊨ (φ ∧ ψ)
testSeq {σ} = ∧-i {!  !} {!   !}
