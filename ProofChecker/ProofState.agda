module ProofState where

open import Lists
open import Proc
open import Props
open import Program

data Rule : Set where

record ProofState : Set where
  constructor proofState
  field
    program : Prog
    truths : List (List Props)
    proof : List Rule
    goal : Props
