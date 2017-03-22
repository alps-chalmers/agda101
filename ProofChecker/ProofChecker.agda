module ProofChecker where

open import Bool
open import Lists
open import Nat
open import Props
open import MapFold
open import Program
open import LTL
open import Translator
open import Label
open import Rules

-- Proof step is a step or a list of steps

{-# BUILTIN NATURAL Nat #-}

-- TODO Add condition rule for branching.

data ProofStep : Set where
  pStep : Rule → ProofStep
  branch : List ProofStep → List ProofStep → ProofStep

data Proof : Set where
  proof : List ProofStep → Proof

branchProof : Proof
branchProof = proof pr
  where
    step1 = pStep (assRule T)
    step2 = pStep (assRule T)
    step3-11 = pStep (assRule T)
    step3-12 = pStep (assRule T)
    step3-2 = pStep (assRule T)
    step3 = branch (step3-11 :: (step3-12 :: [])) (step3-2 :: [])
    step4 = pStep (assRule T)
    pr    = step1 :: (step2 :: (step3 :: (step4 :: [])))


{- A Promela program

int x;
int y;

s0:  init{
s1: run A();
    run B();
}

proctype A(){
s2:  x = 1;
}

proctype B(){
s3:  y = 1;
}

goal: <> (x == 1)
-}

-- Agda representation of the Program program
program : Prog
program = prog main
  where
      s1 = seg (s 2) < (vN 0) :=n nat 1 >
      s2 = seg (s 3) < (vN 1) :=n nat 1 >
      main = block (s 0) (par (s 1) (s1 :: (s2 :: [])) :: [])

-- Proof for the Promela Program
proof1 : Proof
proof1 = proof (r1 :: (r2 :: (r3 :: (r4 :: (r5 :: [])))))
  where
    r1 = pStep (seqRule (at (s 0)))
    r2 = pStep (parRule (at (s 1)))
    r3 = pStep (andRule1 ((at (s 2)) ∧ (at (s 3))))
    r4 = pStep (assRule (at (s 2)))
    r5 = pStep (andRule2 (at (s 2) ∧ (0 EQ 1)))


{-# TERMINATING #-}

-- Tries to apply the rule for a step in the proof.
-- takeStep : Program translation → Proof step → Current truth → Resulting LTL
takeStep : List TransRel → ProofStep → LTL → LTL
takeStep prg (pStep r) Γ = applyRule prg Γ r
takeStep prg (branch b₁ b₂) Γ = if isEq res1 res2 then res1 else ⊥
  where
    res1 = foldl (λ Γ step → takeStep prg step Γ) Γ b₁
    res2 = foldl (λ Γ step → takeStep prg step Γ) Γ b₂

-- Checks whether a given proof holds for a given program.
-- proofCheck : program → proof → goal → entry point → Resulting Boolean
proofCheck : Prog → Proof → LTL → LTL → Bool
proofCheck _ _ T _ = true
proofCheck _ _ ⊥ _ = false
proofCheck prg pr (□ φ) Γ = false -- TODO add box, maybe prove termination and still holds?
proofCheck prg pr (φ ⇒ ψ) _ = proofCheck prg pr ψ φ
proofCheck prg (proof stps) (◇ φ) Γ = isEq φ (foldl (λ Γ stp → if isEq ⊥ Γ then Γ else takeStep (translate program) stp Γ) Γ stps)
proofCheck prg _ φ Γ = isEq φ Γ
