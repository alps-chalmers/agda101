module Tutorial2 where

data Bool : Set where
  true : Bool
  false : Bool

_&&_ : Bool -> Bool -> Bool
true && true = true
_ && _ = false

_||_ : Bool -> Bool -> Bool
false || false = false
_ || _ = true

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

one = succ zero
two = succ one

add : Nat -> Nat -> Nat
add zero y = y
add (succ x) y = succ (add x y)-- add x (succ y)

data _≡_ {A : Set} (a : A) : A -> Set where
  refl : a ≡ a

trans : {A : Set} -> {a1 a2 a3 : A} -> a1 ≡ a2 -> a2 ≡ a3 -> a1 ≡ a3
trans refl refl = refl
