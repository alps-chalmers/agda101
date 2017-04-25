module Proofs where

open import Bool
open import N
open import Props
open import Program
open import HoareLogic

{- Quotient and Remainder - C.A.R. Hoare 1969 p. 578
  a:  r := x;
  b:  q := 0;
  c:  while y <= r do
        d:  r := r - y;
        e:  q := q + 1
-}

-- Variables and constants

x = (nvar N0)
y = (nvar N1)
r = (nvar N2)
q = (nvar N3)

X = rvarN (nvar N0)
Y = rvarN (nvar N1)
R = rvarN (nvar N2)
Q = rvarN (nvar N3)

n0 = constN N0

-- Proof

L1 = axiom (⊤ ⊃ (beval (X N= (X N+ (Y N* n0)))))
S21 = (beval (X N= (X N+ (Y N* n0))))
L2 = D0-n S21 r X
S31 = (beval (X N= (R N+ (Y N* n0))))
L3 = D0-n S31 q n0
L4 = D1-b L1 L2
--L5 = D2 L4 L3 --funkar inte för D0-n byter ut det första x:et i beviset.... :/
