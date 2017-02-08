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
  P : Nat -> Pred

data Formula : Set where
  pred : Pred -> Formula
  <>_ : Formula -> Formula
  [#]_ : Formula -> Formula
  _=>_ : Formula -> Formula -> Formula
  _eqN_ : String -> Nat -> Formula
  bottom : Formula

data Var : Set where
  iVar : Nat -> Var
  bVar : Bool -> Var

data Trans : Set where
  nothing : Trans
  _==>_ : Pred -> Formula -> Trans


-- TODO Add the actual proof to the state!

record State : Set where
  constructor state
  field
    trans : List Trans
    facts : List Formula
    goal : Formula

postulate primStringEquality : String → String → Bool

candidates : Pred -> State -> List Formula
candidates p (state trans facts goal) = filter (λ x → true) facts -- TODO not true

-- eval p (state trans facts goal) = {!   !}

eqForm : Formula -> Formula -> Bool
eqForm (x1 eqN n1) (x2 eqN n2) = primStringEquality x1 x2 && (n1 == n2)
eqForm _ _ = false

lookup : Formula -> List Formula -> Bool
lookup v [] = false
lookup (x1 eqN n1) ((x2 eqN n2) :: ls) = if (eqForm (x1 eqN n1) (x2 eqN n2)) then true else lookup (x1 eqN n1) ls
lookup v (_ :: ls) = lookup v ls

goalReached : State -> Bool
goalReached (state trans fs goal) = foldl (λ b f → b || eqForm f goal) false fs

assume : Formula -> State -> State
assume f (state trans facts goal) = state trans (add f facts) goal
