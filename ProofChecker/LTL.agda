module LTL where

open import Label
open import Data.Nat
open import Data.Bool

-- Extended LTL

data LTL : Set where
  T' ⊥        : LTL
  ∼           : LTL → LTL
  □ ◇         : LTL → LTL
  _∧'_ _∨'_   : LTL → LTL → LTL
  _⇒_         : LTL → LTL → LTL
  _~>_        : LTL → LTL → LTL
  at in' after : Label → LTL
  _EQ_        : ℕ → ℕ → LTL
  isTrue      : ℕ → LTL
