module Program where

open import N
open import Bool

data BVar : Set where
  bvar : N -> BVar

data NVar : Set where
  nvar : N -> NVar

data NExpr : Set where
  static : NExpr -> NExpr
  _N+_   : NExpr -> NExpr -> NExpr
  _N-_   : NExpr -> NExpr -> NExpr
  _N*_   : NExpr -> NExpr -> NExpr
  constN : N -> NExpr
  rvarN  : NVar -> NExpr

data BExpr : Set where
  constB : Bool -> BExpr
  rvarB  : BVar -> BExpr
  _N>_   : NExpr -> NExpr -> BExpr
  _N<_   : NExpr -> NExpr -> BExpr
  _N>=_  : NExpr -> NExpr -> BExpr
  _N<=_  : NExpr -> NExpr -> BExpr
  _N=_   : NExpr -> NExpr -> BExpr

data Statement : Set where
  assignN     : NVar -> NExpr -> Statement
  assignB     : BVar -> BExpr -> Statement
  assignment  : Statement
  composition : Statement -> Statement -> Statement
  while       : BExpr -> Statement -> Statement
  -- cobegin     : Statement -> Statement -> Statement
