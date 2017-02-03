module ProofChecker where

open import State
open import Nat
open import Lists
open import Bool
open import MapFold

basicState : State
basicState = record { trans = ((P "s2") ==> (<>("x" eqN succ zero))) :: ( ((P "s1") ==> (<> (pred (P "s2")))) :: [])
                    ; facts = ("x" eqN zero) :: []
                    ; goal = pred (P "s1") => (<> ("x" eqN succ zero))
                    }


find<> : State -> State
find<> s = {! filter  !}

findPath : State -> Trans
findPath s = ?

prove' : State -> State
prove' s = if goalReached s then s else prove' (findPath s)

prove : State -> State
prove (state trans facts (pred x)) = {!   !}
prove (state trans facts (<> goal)) = {! find<>   !}
prove (state trans facts ([-] goal)) = {!   !}
prove (state trans facts (p => q)) = prove' (assume p (state trans facts q))
prove (state trans facts (x eqN x₁)) = {!   !}


proveBasic : State
proveBasic = prove basicState

{-
// BASIC

int x = 0;

init{
s1: run A();
s3  assert (<>x==1)
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
