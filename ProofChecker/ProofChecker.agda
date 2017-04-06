{-
  Does the actual verifying of proofs. Contains data types for Proofs and functions for verification
-}
module ProofChecker where

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

-- Proof step is a step or a list of steps

-- TODO Add condition rule for branching.

data ProofStep : Set where
  pStep : Rule → ProofStep
  branch : Rule → List ProofStep → List ProofStep → ProofStep

data PStep : Set where
  pStep2 : {φ : LTL} → Ru φ → PStep

data Proof : Set where
  proof : List ProofStep → Proof

{-# TERMINATING #-}

-- Tries to apply the rule for a step in the proof.
-- takeStep : Program translation → Proof step → Current truth → Resulting LTL
takeStep : List TransRel → ProofStep → ValidProof → ValidProof
takeStep _ _ (no err) = no err
takeStep prg (pStep r) (yes φ) = applyRule prg φ r
takeStep prg (branch x b₁ b₂) (yes φ) = case res1 of λ
  { (yes ψ₁) → case res2 of λ
    { (yes ψ₂) → if isEq ψ₁ ψ₂ then yes ψ₁ else no "Mismatch of conclusions"
    ; err → err
    }
  ; err  → err
  }
  where
    res1 = foldl (λ Γ step → takeStep prg step Γ) (yes φ) b₁
    res2 = foldl (λ Γ step → takeStep prg step Γ) (yes φ) b₂

-- Checks whether a given proof holds for a given program.
-- proofCheck : program translation → proof → goal → known → Resulting Boolean
proofCheck' : List TransRel → Proof → LTL → LTL → ValidProof
proofCheck' _ _ T' _ = yes T'
proofCheck' _ _ ⊥ _ = no "Bot always false"
proofCheck' rels pr (□ φ) Γ = no "TODO" -- TODO add box, maybe prove termination and still holds?
proofCheck' rels pr (φ ⇒ ψ) _ = proofCheck' rels pr ψ φ
proofCheck' rels (proof stps) (◇ φ) Γ = case res of λ
  { (yes ψ) → if isEq φ ψ then yes (◇ φ) else no ("Wrong conclusion, " String.++ (pLTL φ) String.++ " is not the same as " String.++ (pLTL ψ) String.++ ".")
  ; err → err
  }
  where res = foldl (λ t stp → takeStep rels stp t) (yes Γ) stps
proofCheck' rels _ φ Γ = if (isEq φ Γ) then yes φ else no "Not true in the initial state"

{-takes a program, custom rules, a proof, a goal and a truth. Returns wether or not the proof is valid given everything else.-}
proofCheck : Prog → List TransRel → Proof → LTL → LTL → ValidProof
proofCheck pr rels g Γ = proofCheck' ((translate pr) List.++ rels) g Γ

