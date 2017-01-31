module ProofChecker where

open import Nat
open import Bool
open import Lists
open import Env
open import MapFold

{-
int x = 0;

proctype A(){
  x = 1;
}

proctype B(){
  x = 2;
}

init{
  run A();
  run B();
  // Prove <> (x==2)
}

-}

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

holds : LTL -> Bool
holds l = true

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
assert e P = {!   !}
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
