module ProofState where

open import Lists
open import Proc
open import LTL
open import Program

data Rule : Set where
  --rule :

record ProofState : Set where
  constructor proofState
  field
    program : Prog
    truths : List LTL
    proof : List Rule
    goal : LTL
