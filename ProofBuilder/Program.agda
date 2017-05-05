
-- Module used for representing concurrent Procrams in agda.

module Program where

open import Data.Nat
open import Data.Bool
open import Data.String
open import LTL
open import Label

-- A process starting at at label i
data Proc : (p : Label) → (l : Label) → Set where
  proc : (p : Label) → (l : Label) → Proc p l

-- Program statement representation.
data Stm : Set where
  _:=n_ : (x : String) → (n : ℕ*) → Stm     -- Nat assignment
  _:=b_ : (x : String) → (b : Bool*) → Stm  -- Bool assignment
  _||_  : ∀{p₁ p₂ a b} → Proc p₁ a → Proc p₂ b → Stm   -- a and b exectued in parallel
  if    : (b : Bool*) → (l : Label) → Stm   -- if-statement
  while : (b : Bool*) → (l : Label) → Stm   -- while-statement
  fin   : ∀{p s} → (pr : Proc p s) → Stm

-- Segment representation. A segment is a labled statement and belongs to a process.
data Seg : Label → Stm → Label → Set where
  seg : (l₁ : Label) → (stm : Stm) → (l₂ : Label) → Seg l₁ stm l₂

-- Program representation. Takes a single main process as argument.
data Prog : {p l : Label} → (ps : Proc p l) → ℕ → Set where
  prog : {p l : Label} → (ps : Proc p l) → Prog ps 0
  _⋆_  : ∀{n} {p l : Label} {ps : Proc p l} → (pr : Prog ps n) → (φ : LTL) → Prog ps (suc n)
