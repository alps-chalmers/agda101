module Env where

open import Nat
open import Bool
open import Lists

data String : Set where
  a : String
  b : String
  c : String

data Var : Set where
    int : String -> Nat -> Var

val : String -> Nat
val a = zero
val b = succ zero
val c = succ (succ zero)

id : Var -> String
id (int s _) = s

_eqs_ : String -> String -> Bool
s1 eqs s2 = (val s1) == (val s2)

_eq_ : Var -> Var -> Bool
int s1 n1 eq int s2 n2 = (s1 eqs s2) && (n1 == n2)

data Env : Set where
  env : List Var -> Env

add : Env -> Var -> Env
add (env vs) v = env (v :: vs)

update' : List Var -> Var -> List Var
update' [] _ = []
update' (x :: xs) v = if x eq v then v :: xs else (x :: (update' xs v))

update : Var -> Env -> Env
update v (env xs) = env (update' xs v)

elem : Env -> Var -> Bool
elem (env []) v = false
elem (env (x :: xs)) v = if (x eq v) then true else (elem (env xs) v)

find' : String -> List Var -> Var
find' s [] = int a zero
find' s (x :: xs) = if id x eqs s then x else (find' s xs)

find : String -> Env -> Var
find s (env xs) = find' s xs
