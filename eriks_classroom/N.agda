module N where
import Bool
open Bool

data N : Set where
  zero : N
  suc  : N -> N

_+_ : N -> N -> N
zero + n = n
(suc n) + m = n + (suc m)

_<_ : N -> N -> Bool
_    < zero    = false
zero < (suc n) = true
(suc n) < (suc m) = n < m

_>_ : N -> N -> Bool
n > m = not (n < m)

min : N -> N -> N
min x y with x < y
min x y | true = x
min x y | false = y

