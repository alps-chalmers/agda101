module Program where

open import N
open import Bool

Label = N

module Labels where
  a = N0
  b = N1
  c = N2
  d = N3
  e = N4
  f = N5
  g = N6
  h = N7
  i = N8

data BVar : Set where
  bvar : N -> BVar

data NVar : Set where
  nvar : N -> NVar

data BExpr : Set where
  constB : Bool -> BExpr
  rvarB  : N -> BExpr

data NExpr : Set where
  constN : N -> NExpr
  rvarN  : N -> NExpr


data Statement : Set where
  -- <_:=_>n      : NVar -> NExpr -> Statement
  -- <_:=_>b      : BVar -> BExpr -> Statement
  assignment : Statement


data Seg : Set where
  stm : Label -> Statement -> Seg
  seg : Label -> Statement -> Seg -> Seg
  while cond : Label -> BExpr -> Seg -> Seg
  cobegin : Label -> Seg -> Seg -> Seg

label : Seg -> Label
label (stm l _) = l
label (seg l _ _) = l
label (while l _ _) = l
label (cond l _ _) = l
label (cobegin l _ _) = l

data Program : Set where
  program : Seg -> Program


