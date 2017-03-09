module TestProg1 where

--open import Nat
open import Bool
open import Lists
open import Data.Nat
open import Program
-- {-# BUILTIN NATURAL Nat #-}

s1 s2 s3 s4 s5 : Seg
s1 = seg (s 1) < (vN 0) :=n (nat 0) >
s2 = seg (s 2) < (vN 1) :=n (nat 0) >
s4 = seg (s 4) < (vN 0) :=n (nat 1) >
s5 = seg (s 5) < (vN 1) :=n (nat 1) >
s3 = par (s 3) (s4 :: (s5 :: empty))

p : Prog
p = prog (block (s 0) (s1 :: (s2 :: (s3 :: empty))))

