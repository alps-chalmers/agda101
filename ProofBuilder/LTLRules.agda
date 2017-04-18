module LTLRules where

open import LTL
open import Label

data LTLRule : LTL → LTL → Set where
  ∧-e₁    : {φ ψ : LTL} → LTLRule (φ ∧' ψ) φ
  ∧-e₂    : {φ ψ : LTL} → LTLRule (φ ∧' ψ) ψ
  ⊥-e     : {φ : LTL} → LTLRule ⊥ φ
  in⇒at   : {l : Label} → LTLRule (in' l) (at l)
  □⇒~>    : {φ ψ : LTL} → LTLRule (□(φ ⇒ ψ)) (φ ~> ψ)
  □-∧-exp : {φ ψ : LTL} → LTLRule (□(φ ∧' ψ)) ((□ φ) ∧' (□ ψ))
  □-∨-exp : {φ ψ : LTL} → LTLRule (□(φ ∨' ψ)) ((□ φ) ∨' (□ ψ))
  ◇-∧-exp : {φ ψ : LTL} → LTLRule (◇(φ ∧' ψ)) ((◇ φ) ∧' (◇ ψ))
  ◇-∨-exp : {φ ψ : LTL} → LTLRule (◇(φ ∨' ψ)) ((◇ φ) ∨' (◇ ψ))
  TL5     : {φ ψ : LTL} → LTLRule ((□ φ) ∧' (□ (φ ⇒ ψ))) (□ ψ)
  TL6     : {φ : LTL} → LTLRule T' ((◇ φ) ∨' (□ (∼ φ)))
