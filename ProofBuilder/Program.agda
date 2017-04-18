module Program where

open import Label
open import Data.Nat
open import Data.String

data Exp : Set where
  _:=_ : (x : String) → (n : ℕ) → Exp
  _||_ : (a : Label) → (b : Label) → Exp

data Stm : Label → Exp → Label → Set where
  reg : (l₁ : Label) → (e : Exp) → (l₂ : Label) → Stm l₁ e l₂
  par : {a₁ a₂ b₁ b₂ : Label} {e₁ e₂ : Exp} → (l₁ : Label) → Stm a₁ e₁ a₂ → Stm b₁ e₂ b₂ → (l₂ : Label) → Stm l₁ (a₁ || b₁) l₂
