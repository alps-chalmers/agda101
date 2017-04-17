module LTLRules where

open import LTL

data LTLRule : LTL → LTL → Set where
  ∧-e₁    : {φ ψ : LTL} → LTLRule (φ ∧' ψ) φ
  ∧-e₂    : {φ ψ : LTL} → LTLRule (φ ∧' ψ) ψ
  ⊥-e     : {φ : LTL} → LTLRule ⊥ φ
