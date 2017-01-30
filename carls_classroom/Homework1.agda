module Homework1 where

-- Problem 1:
data Bool : Set where
  true : Bool
  false : Bool

_||_ : Bool -> Bool -> Bool
false || false = false
_ || _ = true

_imp_ : Bool -> Bool -> Bool
true imp false = false
_ imp _ = true


-- Problem 2:
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

-- (a)
equal : Nat -> Nat -> Bool
equal zero zero = true
equal zero _ = false
equal _ zero = false
equal (suc n) (suc m) = equal n m

iseven : Nat -> Bool
iseven zero = true
iseven (suc zero) = false
iseven (suc (suc n)) = iseven n

-- (b)
_+_ : Nat -> Nat -> Nat
zero + n = n
(suc n) + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero * m = zero
(suc n) * m = m + (n * m)


-- Problem 3:
data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A -> Maybe A

data List (A : Set) : Set where
  [] : List A
  _::_ : A -> List A -> List A

tail : {A : Set} -> List A -> Maybe (List A)
tail [] = Nothing
tail (x :: []) = Just (x :: [])
tail (x :: xs) = Just xs

last : {A : Set} -> List A -> Maybe A
last [] = Nothing
last (x :: []) = Just x
last (x :: xs) = last xs


-- Problem 4:
zipwith : {A B C : Set} -> (A -> B -> C) -> List A -> List B -> List C
