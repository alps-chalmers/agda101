module Integer where

open import Nat

data Integer : Set where
  -[1+_] : Nat -> Integer
  +_ : Nat -> Integer
