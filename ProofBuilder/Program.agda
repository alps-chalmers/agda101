
-- Module used for representing concurrent programs in agda.

module Program where

open import Label
open import Data.Nat
open import Data.String
open import Data.Bool
open import LTL

-- Program statement representation.
data Stm : Set where
  _:=n_ : (x : String) → (n : ℕ*) → Stm
  _:=b_ : (x : String) → (b : Bool*) → Stm
  _||_  : (a : Label) → (b : Label) → Stm
  if    : (b : Bool*) → (s : Label) → Stm
  while : (b : Bool*) → (s : Label) → Stm

-- Program segment representation. A segment is a labled statement.
data Seg : Label → Stm → Label → Set where
  seg : (l₁ : Label) → (stm : Stm) → (l₂ : Label) → Seg l₁ stm l₂
