module AgdaBasics where

-- Booleans
data Bool : Set where
  true : Bool
  false : Bool

-- Natural numbers
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + n = n
(suc n) + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero * _ = zero
suc n * m = m + (n * m)

-- List
infixr 40 _::_
data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

identity  : (A : Set) -> A -> A
identity A x = x

-- identityvar_and_ : (A : Set) -> A -> A
-- identityvar A and x = x

fun[_] : (A : Set) -> Nat
fun[ _ ] = zero

booltest : Bool -> Nat
booltest true = zero
booltest false = suc zero

applynat : (A : Set) -> (F[_] : A -> Nat) -> A -> Nat
applynat A F[_] n = F[ n ]

applyarb : (A : Set) -> (F[_] : A -> Set) -> A -> Set
applyarb A F[_] var = F[ var ]














apply : (A : Set) -> (B : A -> Set) -> ((x : A) -> B x) -> (a : A) -> B a
apply A B f a = f a

zero' : Nat
zero' = identity Nat zero

