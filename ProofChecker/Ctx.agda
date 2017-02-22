module Ctx where

open import Nat
open import Props

data Ctx : Nat → Set where
  ∅ : Ctx zero
  _⋆_ : {n : Nat} → Ctx n → Props → Ctx (succ n)
