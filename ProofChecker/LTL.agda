module LTL where

open import Props
open import Label
open import Nat
open import Bool

-- Extended LTL

data _≡_ {A : Set} : A → A → Set where
  refl : (a : A) → a ≡ a

data LTL : Set where
  T ⊥         : LTL
  -- prop        : Props → LTL
  ∼           : LTL → LTL
  □ ◇         : LTL → LTL
  _∧_ _∨_     : LTL → LTL → LTL
  _⇒_         : LTL → LTL → LTL
  _~>_        : LTL → LTL → LTL
  at in' after : Label → LTL
  _EQ_        : Nat → Nat → LTL
  isTrue      : Nat → LTL
