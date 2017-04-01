module Ctx where

open import Data.Nat
open import Props

data Ctx : ℕ → Set where
  ∅   : Ctx zero
  _⋆_ : {n : ℕ} → Ctx n → Props → Ctx (suc n)
