module ProofChecker where

open import Bool
open import Lists
open import Nat
open import Proc
open import Props
open import MapFold
open import Program
open import LTL
open import Translator
open import Label
open import Rules

-- Proof step is a step or a list of steps

{-# BUILTIN NATURAL Nat #-}

record Proof : Set where
  constructor proof
  field
    steps : List Rule
    goal  : LTL

proof1 : Proof
proof1 = proof (r1 :: (r2 :: (r3 :: (r4 :: (r5 :: empty))))) (◇ (0 EQ 1))
  where
    r1 = seqRule (at (s 0))
    r2 = parRule (at (s 1))
    r3 = andRule1 ((at (s 2)) ∧ (at (s 3)))
    r4 = assRule (at (s 2))
    r5 = andRule2 (at (s 2) ∧ (0 EQ 1))

proof2 : Proof
proof2 = proof (r1 :: (r2 :: (r3 :: (r4 :: (r5 :: empty))))) ((at (s 0)) ⇒ (◇ (1 EQ 1)))
  where
    r1 = seqRule (at (s 0))
    r2 = parRule (at (s 1))
    r3 = andRule1 ((at (s 2)) ∧ (at (s 3)))
    r4 = assRule (at (s 2))
    r5 = andRule2 (at (s 2) ∧ (0 EQ 1))

proof3 : Proof
proof3 = proof empty ((at (s 2)) ⇒ (at (s 2)))

proof4 : Proof
proof4 = proof empty T

program : Prog
program = prog main
  where
        s1 = seg (s 2) < (vN 0) :=n nat 1 >
        s2 = seg (s 3) < (vN 1) :=n nat 1 >
        main = block (s 0) (par (s 1) (s1 :: (s2 :: empty)) :: empty)

isProven : LTL → List LTL -> Bool
isProven φ ls = elem φ ls isEq

{-# TERMINATING #-}

proofCheck : Prog → Proof → List LTL → Bool
proofCheck prg pf truths with Proof.goal pf
... | T = true
... | ⊥ = false
... | φ ⇒ ψ = proofCheck prg (proof (Proof.steps pf) ψ) (ψ :: truths)
... | ◇ φ = isProven φ (foldl (λ ltls r → (applyRule (translate prg) ltls r) :: empty) truths (Proof.steps pf))
... | □ φ = false -- TODO add box
... | φ = elem φ truths isEq


{- The Promela program for this proof

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
