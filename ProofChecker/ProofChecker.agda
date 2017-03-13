module ProofChecker where

open import ProofState
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

{-# BUILTIN NATURAL Nat #-}


program : Prog
program = prog main
  where -- init = < vN 0 :=n nat 0 > :: (< vN 1 :=n nat 0 > :: empty)
        s1 = seg (s 2) < (vN 0) :=n nat 1 >
        s2 = seg (s 3) < (vN 1) :=n nat 1 >
        main = block (s 0) (par (s 1) (s1 :: (s2 :: empty)) :: empty)

-- trans : Prog -> List Entails
-- trans p = translate p

step2 : List TransRel → List LTL → LTL
step2 rel truths = applyRule rel ((at (s 1)) :: empty) (parRule (at (s 1)))

step1 : List TransRel → List LTL → LTL
step1 rel truths = step2 rel (result :: empty)
  where result = applyRule rel truths (seqRule (at (s 0)))

prove : LTL
prove = step1 (translate program) ((at (s 0)) :: empty)



-- (translate' init) ++ (translate main)

{-}
applyRule : ProofState -> Rule -> ProofState
applyRule ps r = {!   !}

isProven : ProofState -> Bool
isProven ps = {!   !}

proofCheck : ProofState -> Bool
proofCheck ps = isProven (foldl (λ ps' r → applyRule ps' r) ps (ProofState.proof ps))
-}
{- The Promela program for this proof

int x = 0;
int y = 0;

init{
a:  x = 1;
b:  run A();
    run B();
}

a proc A(){
c:  x = 2;
}

a proc B(){
d:  y = 1;
}

goal: <> (x == 2)
extended goal: a =~> x==2

-}
