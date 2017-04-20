module Statement where

open import N
open import Bool


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
  assignN      : NVar -> NExpr -> Statement
  assignB      : BVar -> BExpr -> Statement
  assignment : Statement
  composition : Statement -> Statement -> Statement
  while : BExpr -> Statement -> Statement
  cobegin : Statement -> Statement -> Statement

