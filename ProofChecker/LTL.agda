module LTL where

open import Props

-- Extended LTL

data LTL : Set where
  T ⊥       : LTL
  prop      : Props → LTL
  ∼_        : LTL → LTL
  □ ◇       : LTL → LTL
  _∧_ _∨_   : LTL -> LTL -> LTL
  _⇒_       : LTL → LTL -> LTL
  _~>_      : LTL → LTL → LTL
