module TestLogic where

open import Imports
open import Logic


-- prove P 0 => P 2

basicLemmas : List Prop
basicLemmas = ((P O) => (P (O +1))) , (((P (O +1)) => (P ((O +1) +1))) , [])

basicProofSteps : List Rule
basicProofSteps = (assume (P O)) , ((->e (P O) ((P O) => (P (O +1)))) , ((->e (P (O +1)) (((P (O +1)) => (P ((O +1) +1)))) , [])))

basicProof : Proof
basicProof = record { propositions = basicLemmas ; proven = [] ; steps = basicProofSteps ; goal = (P O) => (P ((O +1) +1))}

-- C-c C-n and test check (fix basicProof)

