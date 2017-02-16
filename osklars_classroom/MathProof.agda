module MathProof where

open import Imports

--rules

data Val : Set where
  v : Nat → Nat → Val
  --goal : v O y

f : Val → Val
f (v O y) = v O y
f (v (n +1) y) = v n y

data Real : Val → Set where
  start : Real (v (((O +1) +1) +1) (O +1))
  next : {v : Val} → Real v → Real (f v)

data xfixed : Nat → Set where
  correct : {x y : Nat} → Real (v x y) → xfixed x






-- Let's find a way to force me to prove iterating eventually leaves x==0
{-
eventuallyzero : {v : Val} → Real v → xfixed O
eventuallyzero (next (v (O +1) y)) = correct (Real (v O y))
eventuallyzero r = eventuallyzero (next r)
-}
