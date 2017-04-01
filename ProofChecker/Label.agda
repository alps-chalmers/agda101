module Label where

open import Data.Nat

data Label : Set where
  s : ℕ -> Label
