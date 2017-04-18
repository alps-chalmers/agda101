module Props where

open import Data.Nat

-- Representation of propositional logic

data Props : Set where
  T ⊥         : Props
  _∧_ _∨_ _⇒_ : Props → Props → Props
  p'          : ℕ → Props
  ~_          : Props → Props
