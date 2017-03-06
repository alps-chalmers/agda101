module LTL where

open import Props
open import Label
open import Nat

-- Extended LTL

data LTL : Set where
  T ⊥         : LTL
  prop        : Props → LTL
  ∼_          : LTL → LTL
  □ ◇         : LTL → LTL
  _∧_ _∨_     : LTL → LTL → LTL
  _⇒_         : LTL → LTL → LTL
  _~>_        : LTL → LTL → LTL
  at after    : Label → LTL
  _EQ_        : Nat → Nat → LTL
