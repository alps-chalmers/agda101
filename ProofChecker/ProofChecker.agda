module ProofChecker where

open import ProofState
open import Bool
open import Lists
open import Nat
open import Proc
open import Props
open import MapFold
open import Program

{-# BUILTIN NATURAL Nat #-}

A : Seg
A = block (seg (s 2) < (vN 0) :=n (nat 2) > :: empty)

B : Seg
B = block (seg (s 3) < (vN 1) :=n (nat 1) > :: empty)

program : Prog
program = prog init main
  where init = < vN 0 :=n nat 0 > :: (< vN 1 :=n nat 0 > :: empty)
        main = block (seg (s 0) < (vN 0) :=n nat 1 > :: (par (s 1) (A :: (B :: empty)) :: empty))


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


{-}
A : Proc
A = proc ([ p 0 :: empty ] := [ (0 n== 1) :: empty ] :: empty)

B : Proc
B = proc ([ p 0 :: empty ] := [ (1 n== 1) :: empty ] :: empty)

C : Proc
C = proc ([ p 0 :: empty ] := [ (0 n== 1) :: empty ] :: ([ p 1 :: empty ] := [ <>(0 n== 2) :: empty ] :: empty))

_parl_ : Proc -> Proc -> Hoare (List Props) Stm
proc empty parl proc p2 = {! p2  !}
proc (x :: p1) parl proc p2 = {!   !}

basicProg : List Proc
basicProg = A :: (B :: empty)

basicProof : List Rule
basicProof = {!   !}

basicState : ProofState
basicState = record {
                    program = basicProg
                    ; truths = empty
                    ; proof = basicProof
                    ; goal = <>(1 n== 1)
                  }

basicState2 : ProofState
basicState2 = record {
                    program = basicProg
                    ; truths = empty
                    ; proof = basicProof
                    ; goal = (v 1 > 1) => (x > 0)
                  }


applyRule : ProofState -> Rule -> ProofState
applyRule pState r = {! r  !}

isValid : ProofState -> Bool
isValid ps' = {!   !}

prove : ProofState -> Bool
prove pState = isValid (foldl (\ s r → applyRule s r) pState (ProofState.proof pState))





-}
