module Alg where
open import N
open import Bool
open import List

record Env : Set where
  constructor env
  field
    x : N
    y : N
    z : N
    p : Bool
    q : Bool


data Var : Set where

data NVar : Var where
  x : NVar
  y : NVar
  z : NVar

data BoolVar : Var where
  p : BoolVar
  q : BoolVar

data Expression : Set where

data NatExpr : Expression where
  
data BoolExpr : Expression where
  equals : NatExpr -> NatExpr -> BoolExpr
  lt     : NatExpr -> NatExpr -> BoolExpr
  gt     : NatExpr -> NatExpr -> BoolExpr
  leq    : NatExpr -> NatExpr -> BoolExpr
  geq    : NatExpr -> NatExpr -> BoolExpr
  bool   : Bool -> BoolExpr
  var    : BoolVar -> BoolExpr

data VoidExpr : Expression where
  load   : Var -> VoidExpr --takes a var from global environment to local 
  set    : Var -> VoidExpr  -- stores local variable in global environment
  add    : NVar -> N -> VoidExpr -- adds N to the variable Var
  inc    : NVar -> VoidExpr -- adds 1 to the varuable var,
  nop    : VoidExpr -- does nothing
  wait   : BoolExpr -> VoidExpr
  branch : BoolExpr -> N -> VoidExpr


data Program : Set where
  program : List Expr -> Program

data State : Set where
  state : Program -> Program -> Env -> State


