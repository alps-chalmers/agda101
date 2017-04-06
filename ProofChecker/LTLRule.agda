module LTLRule where

open import LTL
open import ValidProof

data LTLRule : Set where
  ∧-e₁  : LTLRule
  ∧-e₂  : LTLRule
  ∨-i₁  : LTL → LTLRule
  ∨-i₂  : LTL → LTLRule
