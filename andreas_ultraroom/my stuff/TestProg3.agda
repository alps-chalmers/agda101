module TestProg3 where

--open import Nat
open import Bool
open import Lists
open import Data.Nat
open import Program
-- {-# BUILTIN NATURAL Nat #-}

s0 s1 s2 s3 : Seg
s0 = seg (s 0) < (vN 0) :=n (nat 0) >
--s1 = seg (s 1) < (vN 1) :=n (nat 0) >
s2 = seg (s 2) < (vN 0) :=n (nat 1) >
s3 = seg (s 3) < (vN 0) :=n (nat 2) >
s1 = par (s 1) (s2 :: (s3 :: empty))

p : Prog
p = prog (block (s0 :: (s1 :: empty)))
