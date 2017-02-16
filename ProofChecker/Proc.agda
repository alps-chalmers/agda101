module Proc where

open import Lists
open import Props
open import Nat
open import Bool

data Stm : Set where
  _n=_ : Nat -> Nat -> Stm
  _b=_ : Nat -> Bool -> Stm
  _hold_ : Props -> Stm

record Hoare (A : Set) (B : Set) : Set where
  constructor [_]_[_]
  field pre : A
        action : B
        post : A

data Proc : Set where
  proc : List Props -> Proc

-- applyRule (<>x) = iff {G} pi|pj {D,<>x}
-- applyRule ([]x) = iff {G,x} pi|pj {D,[]x}
