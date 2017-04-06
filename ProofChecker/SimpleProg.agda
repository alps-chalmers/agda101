module SimpleProg where

open import Program
open import Label
open import Data.List

simpleProg : Prog
simpleProg = prog main
  where p1 = seg (s 1) < (vN 0) :=n (nat 0) >
        p3 = seg (s 3) < (vN 0) :=n (nat 1) >
        p4 = seg (s 4) < (vN 0) :=n (nat 2) >
        p2 = par (s 2) (p3 ∷ (p4 ∷ []))
        main = block (s 0) (p1 ∷ p2 ∷ [])
