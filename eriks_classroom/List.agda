module List where
open import N
open import Bool
open import Maybe

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

length : {A : Set} -> List A -> N
length []        = zero
length (x :: xs) = suc (length xs)

empty : {A : Set} -> List A -> Bool
empty []        = true
empty (x :: xs) = false

head : {A : Set} -> List A -> Maybe A
head []       = Nothing
head (x :: _) = Just x

-- indexing a list, returns nothing if index is out of bounds
ix : {A : Set} -> List A -> N -> Maybe A
ix [] _ = Nothing
ix (x :: _) zero = Just x
ix (_ :: xs) (suc n) = ix xs n

-- for fun version of ix, usage xs [ n ]
_[_] : {A : Set} -> List A -> N -> Maybe A
xs [ n ] = ix xs n

filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p [] = []
filter p (x :: xs) with p x
... | true  = x :: filter p xs
... | false = filter p xs

