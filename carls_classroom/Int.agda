module Int where
open import Bool
open import Nat

data Int : Set where
  zero : Int
  suc : Int
  pre : Int

_+_ : Int -> Int -> Int
x + zero = x
zero + y = y
(suc x) + (suc y) = (suc (suc (x + y)))
(pre x) + (pre y) = (pre (pre (x + y)))
(pre x) + (suc y) = x + y
(suc x) + (pre y) = x + y
