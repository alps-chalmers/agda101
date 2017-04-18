module Program where

open import Label
open import Data.Nat
open import Data.String
open import Data.Bool

data Exp : Set where
  _:=_ : (x : String) → (n : ℕ) → Exp
  _||_ : (a : Label) → (b : Label) → Exp
  if   : (b : Bool) → (s : Label) → Exp

data Stm : Label → Exp → Label → Set where
  reg : (l₁ : Label) → (e : Exp) → (l₂ : Label) → Stm l₁ e l₂
  if  : (l₁ : Label) → (b : Bool) → (s : Label) → (l₂ : Label) → Stm l₁ (if b s) l₂
  par : {a₁ a₂ b₁ b₂ : Label} {e₁ e₂ : Exp} → (l₁ : Label) → Stm a₁ e₁ a₂ → Stm b₁ e₂ b₂ → (l₂ : Label) → Stm l₁ (a₁ || b₁) l₂
