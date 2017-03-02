module Either where

data Either (A : Set) (B : Set) : Set where
  Left  : A -> Either A B
  Right : B -> Either A B


