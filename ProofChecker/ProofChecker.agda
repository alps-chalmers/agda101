{-
  Does the actual verifying of proofs. Contains data types for Proofs and
  functions for verification
-}
module ProofChecker where

{-***** imported modules *****-}
open import Data.Bool
open import ValidProof
open import Data.List as List
open import Data.Nat
open import Props
open import Program
open import LTL
open import Translator
open import Label
open import Rules
open import Function
open import Data.String as String
open import LTLRule
{-****************************-}

{-
  Data type for proof steps used in a proof
  -----TODO Add condition rule for branching.-----
-}
data ProofStep : Set where
  pStep : Rule → ProofStep
    -- Regular proof step, uses a rule (see Rules)
  branch : Rule → List ProofStep → List ProofStep → ProofStep
    -- A branch step, used when multiple assumptions has to end up with the
    -- same conclusion. Functions as two sub-proofs

{-
  Data type for a proof
-}
data Proof : Set where
  proof : List ProofStep → Proof -- The proof takes a list of proof steps

{-# TERMINATING #-} --used to guarantee that no infinite loop will occur

{-
  takeStep tries to apply the rule for a step in the proof.
  takeStep : Program translation → Proof step → Current truth → Resulting LTL
-}
takeStep : List TransRel → ProofStep → ValidProof → ValidProof
takeStep _ _ (no err) = no err
  -- If something invalid is passed (see ValidProof), return the ValidProof
  -- 'no' with error message 'err' (see ValidProof)
takeStep prg (pStep r) (yes φ) = applyRule prg φ r
  -- If a regular proofstep is passed with a valid LTL formulae, pass
  -- information to applyRule (see Rules) and returns the result
takeStep prg (branch x b₁ b₂) (yes φ) = case res1 of λ -- Return depends on res1
                                                       -- and res2
  { (yes ψ₁) → case res2 of λ  -- First branch is valid, check result of second
    { (yes ψ₂) → if isEq ψ₁ ψ₂ then yes ψ₁ else no ("Mismatch of conclusions " String.++ (pLTL ψ₁) String.++ " and " String.++ (pLTL ψ₂))
      -- If second branch is valid as well, check if they have the same
      -- conclusion
    ; err → err  -- Second branch invalid, return error message 'err'
    }
  ; err  → err   -- First branch invalid, return error message 'err'
  }
  where
    res1 = foldl (λ Γ step → takeStep prg step Γ) (yes φ) b₁
      -- Accumulates the result of takeStep on the first branch
    res2 = foldl (λ Γ step → takeStep prg step Γ) (yes φ) b₂
      -- Accumulates the result of takeStep on the second branch

{-
  Checks whether a given proof holds for a given program.
  proofCheck : program translation → proof → goal → known → Resulting Boolean
-}
proofCheck' : List TransRel → Proof → LTL → LTL → ValidProof
proofCheck' _ _ T' _ = yes T'
  -- If passed something true, return that it is valid because it's true
proofCheck' _ _ ⊥ _ = no  "⊥ always false."
  -- If passed something false, return that it is invalid because it's false
proofCheck' rels pr (□ φ) Γ = no "TODO □"
  -- Currently not implemented
  -- TODO add box, maybe prove termination and still holds?
proofCheck' rels pr (φ ⇒ ψ) _ = proofCheck' rels pr ψ φ
  -- If passed an implication, replace what is known with LHS of implication and
  -- pass on to itself
proofCheck' rels (proof stps) (◇ φ) Γ = case res of λ
  -- If passed an eventually proof, return depends on res
  { (yes ψ) → if isEq φ ψ then yes (◇ φ) else no ("Wrong conclusion, " String.++ (pLTL φ) String.++ " is not the same as " String.++ (pLTL ψ) String.++ ".")
    -- If the proof is valid and concludes the goal, return that it is valid,
    -- else return that it is invalid with an error message
  ; err → err
    -- If the proof is invalid, return that it is invalid with an error message
  }
  where res = foldl (λ t stp → takeStep rels stp t) (yes Γ) stps
    -- res accumulates the result of takeStep on the proof passed
proofCheck' rels _ φ Γ = if (isEq φ Γ) then yes φ else no ((pLTL φ) String.++ " is not true in the initial state.")
  -- If the goal and what is known if identical, return that it is valid, else
  -- return an error message

{-
  takes a program, custom rules, a proof, a goal and a truth. Returns wether or
  not the proof is valid given the rest of the passed input
-}
proofCheck : Prog → List TransRel → Proof → LTL → LTL → ValidProof
proofCheck pr rels g Γ = proofCheck' ((translate pr) List.++ rels) g Γ
  -- Passes modified input to ProofCheck' (see above)
