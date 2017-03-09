module Lists where

open import Nat
open import Maybe
open import Bool

data List (A : Set) : Set where
  empty : List A
  _::_ : A -> List A -> List A

data Eq (A : Set) : Set where
  _===_ : A -> A -> Eq A
  _/==_ : A -> A -> Eq A

isEmpty : {A : Set} -> List A -> Bool
isEmpty empty = true
isEmpty (x :: xs) = false

add : {A : Set} -> A -> List A -> List A
add x xs = x :: xs

head : {A : Set} -> List A -> Maybe A
head empty = Nothing
head (x :: xs) = Just x

tail : {A : Set} -> List A -> Maybe A
tail empty = Nothing
tail (x :: empty) = Just x
tail (x :: xs) = tail xs

_++_ : {A : Set} -> List A -> List A -> List A
empty ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

_eq_ : {A : Set} {{_ : Eq A}} -> A -> A -> Bool
x eq y = true

elem : {A : Set}  -> A -> List A -> (A -> A -> Bool) -> Bool
elem _ empty _ = false
elem x (y :: ys) f = if (f x y) then true else (elem x ys f)

conc : {A : Set} -> List (List A) -> List A
conc empty = empty
conc (empty :: ls) = conc ls
conc ((x :: ls) :: lss) = x :: (conc (ls :: lss))

data IList (A : Set) : Nat -> Set where
  empty : IList A zero
  _::_ : {n : Nat} -> A -> IList A n -> IList A (succ n)

headI : {A : Set} {n : Nat} -> IList A (succ n) -> A
headI (x :: xs) = x

_+++_ : {A : Set} {n m : Nat} -> IList A n -> IList A m -> IList A (n + m)
empty +++ ys = ys
(x :: xs) +++ ys = x :: (xs +++ ys)

length : {A : Set} {n : Nat} -> IList A n -> Nat
length {A} {n} x = n
