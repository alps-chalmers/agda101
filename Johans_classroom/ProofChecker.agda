module ProofChecker where

open import Nat
open import Bool
open import Lists
open import Env
open import MapFold

{-
int x = 0;

init{
l1:  run A();
l2:  run B();
l5:  x==2;
l6:  assert (l1 => <>l6)
}

proctype A(){
l3:  x = 1;
}

proctype B(){
l4:  x = 2;
}


// To prove : l1 -> <>l6
Premises:

1. <> x == 0
2. l3 -> <> x == 1
3. l4 -> <> x == 2
4. l1 -> <> l3
5. l2 -> <> l4
6. l1 -> <> l2
7. l3 -> <> l2
8. l4 -> <> l5
9. l5 ^ (x==2) -> <> l6

Proof:
------------------
10. l1      assume
11. l4      ->r 4,6
12. <> 15   -> 10,8
13. (x == 2

-}
12.

data Stm : Set where
  assInt : String -> Nat -> Stm

data Proc : Set where
  proc : List Stm -> Proc

data Prog : Set where
  prog : List Proc -> Env -> Prog

data Pred : Set where
  _EQ_ : String -> Nat -> Pred

data LTL : Set where
  ⊥ : LTL
  P : LTL
  _=>_ : LTL -> LTL -> LTL
  _^_ : LTL -> LTL -> LTL
  <>_ : Pred -> LTL
  [-]_ : Pred -> LTL

testEnv : Env
testEnv = env ((int a zero) :: [])

proc1 : Proc
proc1 = proc ((assInt a (succ zero)) :: [])

proc2 : Proc
proc2 = proc ((assInt a (succ (succ zero))) :: [])

testProg : Prog
testProg = prog (proc1 :: []) testEnv

testProg2 : Prog
testProg2 = prog (proc2 :: (proc1 :: [])) testEnv

testProg3 : Prog
testProg3 = prog [] testEnv

execStm : Env -> Stm -> Env
execStm e (assInt s n) = add e (int s n)

execStms : Env -> Proc -> Env
execStms e (proc xs) = foldl execStm e xs

runRandProc : List Proc -> Env -> Env
runRandProc [] e = e
runRandProc ps e = foldl execStms e ps

testLTL : LTL
testLTL = <> (a EQ (succ (succ zero)))

testLTL2 : LTL
testLTL2 = [-] (a EQ zero)

assert : Env -> LTL -> Bool
assert e ⊥ = {!   !}
assert e P = {! per  !}
assert e (ltl => ltl₁) = {!   !}
assert e (ltl ^ ltl₁) = {!   !}
assert e (<> (x EQ y)) = elem e (int x y)
assert (env xs) ([-] (x EQ y)) = foldl (λ { bv n → bv && (int x y eq n) }) true xs

run : Prog -> LTL -> Bool
run (prog x e) ltl = assert e' ltl
  where e' = runRandProc x e

runTest1 : Bool
runTest1 = run testProg testLTL

runTest2 : Bool
runTest2 = run testProg2 testLTL

runTest3 : Bool
runTest3 = run testProg3 testLTL2
