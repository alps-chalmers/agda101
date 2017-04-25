module N where
import Bool
open Bool

data N : Set where
  zero : N
  s    : N -> N

_+_ : N -> N -> N
zero + n = n
(s n) + m = n + (s m)

_==_ : N -> N -> Bool
zero    == zero    = true
zero    == _       = false
_       == zero    = false
(s n) == (s m) = n == m

_<_ : N -> N -> Bool
_    < zero    = false
zero < (s n) = true
(s n) < (s m) = n < m

_>_ : N -> N -> Bool
n > m = not (n < m)

_<=_ : N -> N -> Bool
n <= m = (n < m) or (n == m)

_>=_ : N -> N -> Bool
n >= m = (n > m) or (n == m)

min : N -> N -> N
min x y with x < y
min x y | true = x
min x y | false = y


-- lul xD

N0 = zero
N1 = s N0
N2 = s N1
N3 = s N2
N4 = s N3
N5 = s N4
N6 = s N5
N7 = s N6
N8 = s N7
N9 = s N8
N10 = s N9
N11 = s N10
N12 = s N11
N13 = s N12
N14 = s N13

