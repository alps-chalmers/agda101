module TestProg4 where

open import Bool
open import Lists
open import Data.Nat
open import Program

s1 s2 : Seg
s1 = seg (s 1) < (vN 0) :=n (nat 0) >
s2 = seg (s 2) < (vN 0) :=n (nat 5) >

p : Prog
p = prog (block (s 0) (s1 :: (s2 :: empty)))
