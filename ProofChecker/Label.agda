module Label where

open import Nat

data Label : Set where
  s : Nat -> Label
