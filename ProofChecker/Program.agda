module Program where

open import Lists
open import Nat
open import Bool

data NVar : Set where
  vN : (i : Nat) -> NVar

data BVar : Set where
  vB : (i : Nat) -> BVar

data ExpN : Set where
  nat : Nat -> ExpN
  nVar : NVar -> ExpN

data ExpB : Set where
  bool : Bool -> ExpB
  bVar : BVar -> ExpB

data Exp : Set where
  expN : ExpN -> Exp
  expB : ExpB -> Exp
  _<?_ _<=?_ _>?_ _>=?_ : ExpN -> ExpN -> Exp
  _==n_ : ExpN -> ExpN -> Exp
  _==b_ : ExpB -> ExpB -> Exp

data Stm : Set where
  <_>:=n<_> : NVar -> ExpN -> Stm
  <_:=n_> : NVar -> ExpN -> Stm
  <_>:=b<_> : BVar -> ExpB -> Stm
  <_:=b_> : BVar -> ExpB -> Stm
  wait : Exp -> Stm

data Label : Set where
  s : Nat -> Label

data Seg : Set where
  seg : Label -> Stm -> Seg
  block : List Seg -> Seg
  par : Label -> List Seg -> Seg
  while if : Label -> ExpB -> Seg -> Seg

record Prog : Set where
  constructor prog
  field
    init : List Stm
    main : Seg
