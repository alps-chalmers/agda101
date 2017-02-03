module ProofChecker2 where

open import Bool
open import Nat

postulate
  String : Set

{-# BUILTIN STRING String #-}
{-# COMPILED_TYPE String String #-}

data Var : Set where
  int : String -> Nat -> Var
  bool : String -> Bool -> Var

data Pred : Set where
  P : Pred
  Q : Pred
  R : Pred

data Formula : Set where
  P : Formula
  <>_ : String -> Formula
