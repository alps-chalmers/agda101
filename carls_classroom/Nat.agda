module Nat where
open import Bool

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + y = y
(suc x) + y = suc (x + y)

_-_ : Nat -> Nat -> Nat
zero - y = zero
x - zero = x
(suc x) - (suc y) = x - y

_*_ : Nat -> Nat -> Nat
zero * y = zero
(suc x) * y = y + (x * y)

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < _ = true
(suc x) < (suc y) = x < y

_>_ : Nat -> Nat -> Bool
zero > _ = false
_ > zero = true
(suc x) > (suc y) = x > y

_<=_ : Nat -> Nat -> Bool
x <= y = not (x > y)

_>=_ : Nat -> Nat -> Bool
x >= y = not (x < y)

_==_ : Nat -> Nat -> Bool
x == y = (x <= y) && (x >= y)

_!=_ : Nat -> Nat -> Bool
x != y = not (x == y)

min : Nat -> Nat -> Nat
min x y = if (x < y) then x else y

max : Nat -> Nat -> Nat
max x y = if (x > y) then x else y

iseven : Nat -> Bool
iseven zero = true
iseven (suc zero) = false
iseven (suc (suc n)) = iseven n
