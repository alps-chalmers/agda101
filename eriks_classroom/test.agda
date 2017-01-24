module Test where
open import List
open import Bool
open import N
open import Maybe


lookup : {A : Set} -> (xs : List A) -> (n : N) ->
         isTrue (n < length xs) -> A
lookup []        n       ()
lookup (x :: xs) zero    p = x
lookup (x :: xs) (suc n) p = lookup xs n p

data _==_ {A : Set}(x : A) : A -> Set where
  refl: x == x


data _/=_ : N -> N -> Set where
  z/=s : {n : N} -> zero /= (suc n)
  s/=z : {n : N} -> (suc n) /= zero
  s/=s : {m n : N} -> m /= n -> (suc m) /= (suc n)

data Equal? (n m : N) : Set where
  eq  : n == m -> Equal? n m
  neq : n /= m -> Equal? n m



