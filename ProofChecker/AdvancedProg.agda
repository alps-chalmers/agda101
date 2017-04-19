module AdvancedProg where

{-***** imported modules *****-}
open import Program
open import Label
open import Data.List
open import ProofChecker
open import Rules
open import LTL
open import LTLRule
open import ValidProof
open import Data.Bool
open import Translator
open import Truths
{-****************************-}

{-
  Example of a simple Program (see Program):
prog
(advPrfCheck
  block (s 0)
  (
    seg (s 1) < vB "x" :=b bool true > ∷
    par (s 2)
    (
      seg (s 3) < vB "x" :=b bool false > ∷
      while (s 4) (bVar (vB "x"))
      (
        seg (s 3) < vN "y" :=n nat 1 > ∷
      ) ∷
      []


    ) ∷
    []
  )
)
-}
advProg : Prog
advProg = prog main
  where p1 = seg (s 1) < (vB "x") :=b bool true >
        p3 = seg (s 3) < (vB "x") :=b bool false >
        p5 = seg (s 5) < (vN "y") :=n 1 >
        p4 = while (s 4) (bVar (vB "x")) p5
        p2 = par (s 2) (p3 ∷ (p4 ∷ []))
        main = block (s 0) (p1 ∷ p2 ∷ [])


advProof : Proof
advProof = proof prf
  where
    r1 = pStep (progR (seqRule (at (s 0))))
    -- at s1
    r2 = pStep (progR (assRule (at (s 1))))
    -- after s1 ∧ x
    r3 = pStep (ltlR (∧-e₁ ((after (s 1)) ∧' (isTrue (vB "x")))))
    -- after s1
    r4 = pStep (progR (atomLive (after (s 1))))
    -- at s2
    r5 = pStep (progR (parRule (at (s 2))))
    -- at s3 ∧ at s4
    r6 = pStep (ltlR (exp-∧ ((at (s 3)) ∧' (at (s 4)))))
    -- at s3, at s4
    r7 = pStep (progR (assRule (at (s 3))))
    -- after s3 ∧ ∼ x , at s4
    r8 = pStep (customR 0 (after (s 3) ∧' ∼ (isTrue (vB "x"))) (□ ((after (s 3) ∧' ∼ (isTrue (vB "x"))))))
    -- □ (after s3 ∧ ∼ x) , at s4
    r9 = pStep (progR (whileRule (at (s 4))))
    -- □ (after s3 ∧ ∼ x) , (at s5 ∧ x) ∨ (after s4 ∧ ~ x)
    -- BRANCH 1 - □ (after s3 ∧ ∼ x) , at s5 ∧ x
    r10-1-1 = pStep (ltlR (□-e (□ ((after (s 3)) ∧' (∼ (isTrue (vB "x")))))))
    r10-1 = r10-1-1 ∷ []
    -- BRANCH 2 - □ (after s3 ∧ ∼ x) , after s4 ∧ ∼ x
    r10-2-1 = pStep (ltlR (□-e (□ ((after (s 3)) ∧' (∼ (isTrue (vB "x")))))))
    r10-2 = r10-2-1 ∷ []
    -- BRANCH start
    r10 = branch (ltlR (∨-e (((at (s 5)) ∧' (isTrue (vB "x"))) ∨' ((after (s 4)) ∧' (∼ (isTrue (vB "x"))))))) r10-1 r10-2
    prf = r1 ∷ r2 ∷ r3 ∷ r4 ∷ r5 ∷ r6 ∷ r7 ∷ r8 ∷ r9 ∷ r10 ∷ []


advPrfCheck : ValidProof
advPrfCheck = proofCheck advProg [] advProof ((at (s 0)) ⇒ (◇ (after (s 3) ∧' ∼ (isTrue (vB "x"))))) (truths [])
