module Statement where

open import N
open import Bool
open import Label


data BVar : Set where
  bvar : N -> BVar

data NVar : Set where
  nvar : N -> NVar

data BExpr : Set where
  constB : Bool -> BExpr
  rvarB  : BVar -> BExpr     --read var, just checks value of a bvar

data NExpr : Set where
  constN : N -> NExpr
  rvarN  : NVar -> NExpr


data Statement : Set where
  assignN      : Label -> NVar -> NExpr -> Statement
  assignB      : Label -> BVar -> BExpr -> Statement
  composition : Statement -> Statement -> Statement
  while : Label -> BExpr -> Statement -> Statement
  cobegin : Label -> Statement -> Statement -> Statement

data Program : Set where
  program : Statement -> Program
