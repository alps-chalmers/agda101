module TestProg2 where

open import Bool
open import Lists
open import Data.Nat
open import Program

s0 s1 s2 s3 s4 s5 s6  b0 : Seg
s0 = seg (s 0) < (vN 0) :=n (nat 0) >
--s1 = seg (s 1) < (vN 1) :=n (nat 1) >
s1 = seg (s 1) < (vB 2) :=b (bool true) >
s3 = seg (s 3) < (vN 0) :=n (nat 1) >
s4 = seg (s 4) < (vB 2) :=b (bool false) >
b0 = block (s3 :: (s4 :: empty))
s6 = seg (s 6) < (vN 0) :=n (nat 2) >
s5 = while (s 5) (bVar (vB 2)) (block (s6 :: empty))
s2 = par (s 2) (b0 :: (s5 :: empty))

p : Prog
p = prog (block (s0 :: (s1 :: (s2 :: empty))))
