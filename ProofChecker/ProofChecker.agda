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


{-}
branchProof : Proof
branchProof = proof pr
  where
    step1 = pStep (assRule T)
    step2 = pStep (assRule T)
    step3-11 = pStep (assRule T)
    step3-12 = pStep (assRule T)
    step3-2 = pStep (assRule T)
    step3 = branch (step3-11 ∷ (step3-12 ∷ [])) (step3-2 ∷ [])
    step4 = pStep (assRule T)
    pr    = step1 ∷ (step2 ∷ (step3 ∷ (step4 ∷ [])))
-}

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

{-

program : Prog
program = prog main
  where
      s1 = seg (s 2) < (vN 0) :=n nat 1 >
      s2 = seg (s 3) < (vN 1) :=n nat 1 >
      main = block (s 0) (par (s 1) (s1 ∷ (s2 ∷ [])) ∷ [])


-- Proof for the Promela Program
proof1 : Proof
proof1 = proof (r1 ∷ (r2 ∷ (r3 ∷ (r4 ∷ (r5 ∷ [])))))
  where
    r1 = pStep (seqRule (at (s 0)))
    r2 = pStep (parRule (at (s 1)))
    r3 = pStep (andRule1 ((at (s 2)) ∧' (at (s 3))))
    r4 = pStep (assRule (at (s 2)))
    r5 = pStep (andRule2 (at (s 2) ∧' (0 EQ 1)))

-}





{-programLam : Prog
programLam = prog main
  where p1 = seg (s 3) < (vB 0) :=b bool false >
        p2 = while (s 4) (bVar (vB 0)) (seg (s 5) < (vN 1) :=n nat 1 >)
        main = block (s 0) ( seg (s 1) < (vB 0) :=b bool true > ∷ (par (s 2) (p1 ∷ (p2 ∷ [])) ∷ []))

c1 : TransRel
c1 =  < (after (s 3)) > (custom 1) < (□ ((after (s 2)) ∧' ∼ (isTrue 0))) >

c2 : TransRel
c2 = < after (s 5) > (custom 2) < at (s 4) >

cRuleList : List TransRel
cRuleList = c1 ∷ (c2 ∷ [])

-- < after (s 2) > (custom 1) < □ ((after (s 2)) ∧' (~ (bVar (vB 0)))) ]

proofLam : Proof
proofLam = proof (r1 ∷ (r2 ∷ (r3 ∷ (r4 ∷ (r5 ∷ (r6 ∷ (r7 ∷ [])))))))
  where
    r1 = pStep (seqRule (at (s 0))) -- at s1
    r2 = pStep (assRule (at (s 1))) -- after s1 ∧' x ∧' at s2
    r3 = pStep (parRule (at (s 2))) -- at s3 ∧' at s4
    r4 = pStep (assRule (at (s 3))) -- after s3 ∧' ~x
    r5 = pStep ((customR 1) (after (s 3))) -- □ (after s3 ∧' ~x)
    r6 = pStep (whileRule (at (s 4))) -- in s4 ∨' after s4
    r7-1-1 = pStep (inInf (in' (s 4))) -- at s5 ∨' at s4
    r7-1-2-1-1 = pStep (assRule (at (s 5))) -- after s5 ∧' y == 1
    r7-1-2-1-2 = pStep (∧'-e1 ((after (s 5)) ∧' (1 EQ 1)))
    r7-1-2-1-3 = pStep (customR 2 (after (s 5)))
    r7-1-2-1 = r7-1-2-1-1 ∷ (r7-1-2-1-2 ∷ (r7-1-2-1-3 ∷ []))
    r7-1-2-2 = pStep (dummy (at (s 4))) ∷ []
    r7-1-2 = branch (orRule ((at (s 5)) ∨' at (s 4))) r7-1-2-1 r7-1-2-2
    r7-1-3 = pStep (exitRule (at (s 4) ∧' (∼ (isTrue 0)))) -- after s4
    r7-1-4 = pStep (∧'-i (after (s 3) ∧' after (s 4)))
    r7-1 = r7-1-1 ∷ (r7-1-2 ∷ (r7-1-3 ∷ (r7-1-4 ∷ [])))-- in c
    r7-2-1 = pStep (□-e (□ ((at (s 3)) ∧' (∼ (isTrue 0))))) -- at s3 ∧' ~x
    r7-2-2 = pStep (∧'-e1 ((at (s 3)) ∧' (∼ (isTrue 0))))
    r7-2 = r7-2-1 ∷ (r7-2-2 ∷ [])
    r7 = branch (orRule ((in' (s 4)) ∨' (after (s 4)))) r7-1 r7-2 -- Split in s4 ∨' after s4-}

--------------------

simpleProg : Prog
simpleProg = prog main
  where p1 = seg (s 1) < (vN 0) :=n (nat 0) >
        p3 = seg (s 3) < (vN 0) :=n (nat 1) >
        p4 = seg (s 4) < (vN 0) :=n (nat 2) >
        p2 = par (s 2) (p3 ∷ (p4 ∷ []))
        main = block (s 0) (p1 ∷ p2 ∷ [])

simpleProof : Proof
simpleProof = prf
  where r1 = pStep (progR (seqRule (at (s 0)))) -- at s1
        r2 = pStep (progR (assRule (at (s 1)))) -- after s1 ∧ 0 EQ 0
        r3 = pStep (ltlR (∧-e₁)) -- after s1
        r4 = pStep (progR (atomLive (after (s 1)))) --at s2
        r5 = pStep (progR (parRule (at (s 2)))) --at s3 ∧ at s4
        r6 = pStep (ltlR ∧-e₁) --at s3
        r7 = pStep (progR (assRule (at (s 3)))) --after s3 ∧ 0 EQ 1
        r8 = pStep (ltlR (∧-e₂)) --0 EQ 1
        prf = proof (r1 ∷ (r2 ∷ (r3 ∷ (r4 ∷ r5 ∷ (r6 ∷ r7 ∷ (r8 ∷ [])))))) --0 EQ 1


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
-- proofCheck : program → proof → goal → known → Resulting Boolean
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

proofCheck : Prog → List TransRel → Proof → LTL → LTL → ValidProof
proofCheck pr rels g Γ = proofCheck' ((translate pr) List.++ rels) g Γ

simplePrfCheck : ValidProof
simplePrfCheck = proofCheck simpleProg [] simpleProof ((at (s 0)) ⇒ (◇ (0 EQ 2))) (at (s 7))
