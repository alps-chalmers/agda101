module ProgRules where

open import LTL
open import Label
open import Program
open import Data.String
open import Data.Nat

data ProgRule {x y : Label} {e : Exp} : Stm x e y → LTL → Set where
  -- assRule : {l₁ l₂ : Label} {e : Exp} {x : String} {n : ℕ} → ProgRule Stm l₁ (x := n) l₂ (after l₁ ∧' ("x" ==n n))
  -- flow    : {l₁ l₂ : Label} {e : Exp} → Stm l₁ e l₂ → ProgRule (after l₁) (at l₂)
