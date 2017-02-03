module Lists where

open import Nat
open import Maybe

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

add : {A : Set} -> A -> List A -> List A
add x xs = x :: xs

head : {A : Set} -> List A -> Maybe A
head [] = Nothing
head (x :: xs) = Just x

tail : {A : Set} -> List A -> Maybe A
tail [] = Nothing
tail (x :: []) = Just x
tail (x :: xs) = tail xs

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)


data IList (A : Set) : Nat -> Set where
  empty : IList A zero
  _::_ : (N : Nat) -> IList A (succ N)
