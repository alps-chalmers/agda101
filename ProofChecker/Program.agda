{-
  Program representation
-}
module Program where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Label

{-Data type for integer variables-}
data NVar : Set where
  vN : (i : ℕ) → NVar

{-data type for boolean variables-}
data BVar : Set where
  vB : (i : ℕ) → BVar

{-Data type for expressions regarding integers-}
data ExpN : Set where
  nat : ℕ → ExpN
  nVar : NVar → ExpN

{-Data type for expressions regarding booleans-}
data ExpB : Set where
  bool : Bool → ExpB
  bVar : BVar → ExpB

{-Data type for expressions overall, probably redundant-}
data Exp : Set where
  expN : ExpN → Exp
  expB : ExpB → Exp
  _<?_ _<=?_ _>?_ _>=?_ : ExpN → ExpN → Exp
  _==n_ : ExpN → ExpN → Exp
  _==b_ : ExpB → ExpB → Exp

{-Data type for statements, right now we only use atomic assignments-}
data Stm : Set where
  <_>:=n<_> : NVar → ExpN → Stm
  <_:=n_> : NVar → ExpN → Stm
  <_>:=b<_> : BVar → ExpB → Stm
  <_:=b_> : BVar → ExpB → Stm
  wait : Exp → Stm

{-data type for a code segment. Can be a regular segment, block of code segments, a par statement (cobegin/coend) as well as while loops and if statements.-}
data Seg : Set where
  seg : Label → Stm → Seg
  block : Label → List Seg → Seg
  par : Label → List Seg → Seg
  while if : Label → ExpB → Seg → Seg

{-Label extraction function for each segment constructor-}
label : Seg → Label
label (seg x x₁) = x
label (block x x₁) = x
label (par x x₁) = x
label (while x x₁ x₂) = x
label (if x x₁ x₂) = x

{-Record for program, contains a main segment, should be a block with the rest of the program's segments.-}
record Prog : Set where
  constructor prog
  field
    main : Seg
