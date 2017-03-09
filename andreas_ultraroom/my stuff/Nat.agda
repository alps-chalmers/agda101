module Nat where
open import Bool

data Nat : Set where
  zero : Nat
  succ : Nat -> Nat

{-_+_ : Nat -> Nat -> Nat
zero + y = y
succ x + y = succ (x + y)-}

_+_ : Nat -> Nat -> Nat
zero + y = y
(succ x) + y = succ (x + y)

_-_ : Nat -> Nat -> Nat
zero - y = y
x - zero = x
(succ x) - (succ y) = x - y

_*_ : Nat -> Nat -> Nat
zero * y = zero
succ x * y = y + (x * y)

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < _ = true
(succ x) < (succ y) = x < y

_>_ : Nat -> Nat -> Bool
x > y = not (x < y)

_==_ : Nat -> Nat -> Bool
zero == zero = true
zero == _ = false
succ _ == zero = false
succ x == succ y = x == y
