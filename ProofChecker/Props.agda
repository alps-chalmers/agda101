module Props where

open import Nat

-- Representation of propositional logic

data Props : Set where
  T ⊥ : Props
  _∧_ _∨_ _⇒_ : Props → Props → Props
  p' : Nat → Props
  ~_ : Props → Props
