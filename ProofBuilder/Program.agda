
-- Module used for representing concurrent programs in agda.

module Program where

open import Label
open import Data.Nat
open import Data.String
open import Data.Bool
open import LTL

-- Program statement representation.
data Stm : Set where
  _:=n_ : (x : String) → (n : ℕ*) → Stm     -- Nat assignment
  _:=b_ : (x : String) → (b : Bool*) → Stm  -- Bool assignment
  _||_  : (a : Label) → (b : Label) → Stm   -- a and b exectued in parallel
  if    : (b : Bool*) → (s : Label) → Stm   -- if-statement
  while : (b : Bool*) → (s : Label) → Stm   -- while-statement

-- Program segment representation. A segment is a labled statement.
data Seg : Label → Stm → Label → Set where
  seg : (l₁ : Label) → (stm : Stm) → (l₂ : Label) → Seg l₁ stm l₂

-- A program starting at at label i
data Prog : (i : Label) → (n : ℕ) → Set where
  prog : (i : Label) → Prog i 0
  _⋆_  : ∀{i n} → Prog i n → (φ : LTL) → Prog i (n + 1) -- Represents assumptions
