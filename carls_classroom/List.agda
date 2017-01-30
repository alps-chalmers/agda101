module List where
open import Bool
open import Nat
open import Maybe

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

head : {A : Set} -> List A -> Maybe A
head [] = Nothing
head (x :: _) = Just x

tail : {A : Set} -> List A -> Maybe (List A)
tail [] = Nothing
tail (x :: []) = Just (x :: [])
tail (x :: xs) = Just xs

last : {A : Set} -> List A -> Maybe A
last [] = Nothing
last (x :: []) = Just x
last (x :: xs) = last xs

init : {A : Set} -> List A -> Maybe (List A)
init [] = Nothing
init (x :: []) = Just []
init (x :: xs) = x :: Just (init xs)
