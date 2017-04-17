module Program where

open import Label
open import Data.Nat
open import Data.String

data Exp : Set where
  todo : Exp
  _:=_ : (x : String) → (n : ℕ) → Exp

data Stm : Label → Exp → Label → Set where
  reg : (l₁ : Label) → (e : Exp) → (l₂ : Label) → Stm l₁ e l₂
  par : {l₁ l₂ x y : Label} → Stm l₁ todo x → Stm l₂ todo y → Stm l₁ todo l₂
