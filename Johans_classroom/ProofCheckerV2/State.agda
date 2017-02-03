module State where

open import Nat
open import Bool
open import Lists
open import MapFold

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

data Pred : Set where
  P : String -> Pred

data Formula : Set where
  pred : Pred -> Formula
  <>_ : Formula -> Formula
  [-]_ : Formula -> Formula
  _=>_ : Formula -> Formula -> Formula
  _eqN_ : String -> Nat -> Formula

data Var : Set where
  iVar : Nat -> Var
  bVar : Bool -> Var

data Trans : Set where
  _==>_ : Pred -> Formula -> Trans

record State : Set where
  constructor state
  field
    trans : List Trans
    facts : List Formula
    goal : Formula

eqForm : Formula -> Formula -> Bool
eqForm f1 f2 = true -- TODO

goalReached : State -> Bool
goalReached (state trans fs goal) = foldl (λ b f → b || eqForm f goal) false fs

assume : Formula -> State -> State
assume f (state trans facts goal) = state trans (add f facts) goal
