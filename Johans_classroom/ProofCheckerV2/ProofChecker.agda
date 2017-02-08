{-# OPTIONS --no-termination-check #-}

module ProofChecker where

open import State
open import Nat
open import Lists
open import Bool
open import MapFold

reallyBasicState : State
reallyBasicState = record { trans = ((P (succ zero)) ==> (("x" eqN succ zero))) :: ( ((P zero) ==> ((pred (P (succ zero))))) :: [])
                    ; facts = ("x" eqN zero) :: []
                    ; goal = pred (P zero) => (("x" eqN succ zero))
                    }


basicState : State
basicState = record { trans = ((P (succ zero)) ==> (<>("x" eqN succ zero))) :: ( ((P zero) ==> (<> (pred (P (succ zero))))) :: [])
                    ; facts = ("x" eqN zero) :: []
                    ; goal = pred (P zero) => (<> ("x" eqN succ zero))
                    }


find<> : State -> State
find<> s = {! filter  !}

findPath : State -> Trans
findPath s = {! nothing  !}

prove : State -> Bool
prove s with goalReached s
prove s | true = true
prove (state trans facts (pred x)) | false = {! eval x !}
prove (state trans facts (<> goal)) | false = {!   !}
prove (state trans facts ([#] goal)) | false = {!   !}
prove (state trans facts (p => q)) | false = prove (assume p (state trans facts q))
prove (state trans facts (x eqN n)) | false = lookup (x eqN n) facts
prove (state trans facts bottom) | false = false

proveReallyBasic = prove reallyBasicState

proveBasic : Bool
proveBasic = prove basicState

{-
// BASIC

int x = 0;

init{
s1: run A();
s3: assert (<>x==1)
}

proctype A(){
s2: x = 1;
}

-}

{-
// ADVANCED

int x = 0;

init{
s1:  run A();
s2:  run B();
s5:  assert (<>(x==1 V x==2))
}

proctype A(){
s3:  x = 1;
}

proctype B(){
s4:  x = 2;
}
-}
