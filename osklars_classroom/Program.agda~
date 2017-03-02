module Program where

open import Imports
-- Concurrency

-- p and q

data Pl : Set where
  p1 : Pl
  pend : Pl

data Ql : Set where
  q1 : Ql
  q2 : Ql
  qend : Ql

data Loc : Set where
  l : Pl → Ql → Loc

--x and y

data Val : Set where
  v : Nat → Nat → Val

record State : Set where
  constructor st
  field
    loc : Loc
    val : Val


init : State
init = st (l p1 q1) (v O O)



 -- example:
 -- p1 : x = 1

-- q1 : while x==0
-- q2 : y = y+1 (atomic)

p : State → State
p (st (l p1 q) (v x y)) = st (l pend q) (v (O +1) y)
p s = s -- gets here iff Pl==end

q : State → State
q (st (l p q1) (v O y)) = st (l p q2) (v O y) -- case x==0
q (st (l p q1) (v x y)) = st (l p qend) (v x y) -- else
q (st (l p q2) (v x y)) = st (l p q1) (v x (y +1))
q s = s -- gets here iff Ql==end




data Real : State → Set where
  Start : Real init
  stepp : {s : State} → Real s → Real (p s)
  stepq : {s : State} → Real s → Real (q s)


--I wan't a type that is a state but where x is 1
data xfixed : Nat → Set where
  correct : {x y : Nat} → {l : Loc} → Real (st l (v x y)) → xfixed x


--proof of type box diamond x=1
--with other words: every real state can yeild a state with x=1

proof : {s : State} → Real s → xfixed (O +1)
proof Start = correct (stepp Start)
proof (stepp r) = correct (stepp r)
proof (stepq r) = correct (stepp (stepq r))

































{-
--PSEUDO CODE
data Eventually : State → State → Set where 
 : Eventually

data Always : Bool → Set where
always true : Always

--assumption of program excecution
assumption : State is only constructed through init or p or q.
--assumption of fair scheduler
assumption : {s : State} always eventually (p s) and always eventually (q s)

proof : (real s) implies eventually (x equals (O +1))

use always eventually p of s
case1 : p (loc (pair one _) val _) → x = 1

use state only constructed through init or p or q: state  where 
case2 : p (loc (pair end _) val _) →  x = x (=1 from case1)
-}
