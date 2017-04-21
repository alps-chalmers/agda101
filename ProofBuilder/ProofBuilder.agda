module ProofBuilder where

open import Proof
open import Program
open import Label
open import LTL
open import Data.Bool as Bool using (Bool; true; false)

-- TODO
-- * Index Label over ℕ
-- * Fix fin
-- * Implement if/while



--============================   Simple Program   ==============================

{-
  s0: x = 0
  s1: x = 1
  s2: cobegin
    s3: x = 5
    □
    s4: x = 6
  coend
-}



-- Program representation

s0 : Seg (s 0) ("x" :=n (nat 0)) (s 1)
s0 = seg (s 0) ("x" :=n (nat 0)) (s 1)

s1 : Seg (s 1) ("x" :=n (nat 1)) (s 2)
s1 = seg (s 1) ("x" :=n (nat 1)) (s 2)

s3 : Seg (s 3) ("x" :=n (nat 5)) (fin (s 3))
s3 = seg (s 3) ("x" :=n (nat 5)) (fin (s 3))

s4 : Seg (s 4) ("x" :=n (nat 6)) (fin (s 4))
s4 = seg (s 4) ("x" :=n (nat 6)) (fin (s 4))

s2 : Seg (s 2) ((s 3) || (s 4)) (fin (s 2))
s2 = seg (s 2) ((s 3) || (s 4)) (fin (s 2))

{- Proofs for the program. -}

s0=>s1 : Proof (at (s 0)) → Proof (at (s 1))
s0=>s1 p = flow ( ∧-e₁ (:=n-R p s0)) s0

s1=>s2 : Proof (at (s 1)) → Proof (at (s 2))
s1=>s2 p = flow ( ∧-e₁ (:=n-R p s1)) s1

s2=>s3 : Proof (at (s 2)) → Proof (at (s 3))
s2=>s3 p =  ∧-e₁ (parRule p s2)

s2=>s4 : Proof (at (s 2)) → Proof (at (s 4))
s2=>s4 p =  ∧-e₂ (parRule p s2)

s3=>s3' : Proof (at (s 3)) → Proof (after (s 3))
s3=>s3' p =  ∧-e₁ (:=n-R p s3)

s3=>x==5 : Proof (at (s 3)) → Proof ("x" ==n (nat 5))
s3=>x==5 p = ∧-e₂ (:=n-R p s3)

s4=>s4' : Proof (at (s 4)) → Proof (after (s 4))
s4=>s4' p =  ∧-e₁ (:=n-R p s4)

s2=>s3'∧s4' : Proof (at (s 2)) → Proof ((after (s 3)) ∧ (after (s 4)))
s2=>s3'∧s4' p = ∧-i (s3=>s3' (s2=>s3 p)) (s4=>s4' (s2=>s4 p))

s2=>s2' : Proof (at (s 2)) → Proof (after (s 2))
s2=>s2' p = exitPar (s2=>s3'∧s4' p) s2

-- Final proof of termination
ps0⇒s2' : Proof (at (s 0)) → Proof (after (s 2))
ps0⇒s2' p = s2=>s2' (s1=>s2 (s0=>s1 p))

-- Proof of termination with a different starting point
ps1⇒s2' : Proof (at (s 1)) → Proof (after (s 2))
ps1⇒s2' p = s2=>s2' (s1=>s2 p)

-- Proof of ◇ x==5
ps0⇒x==5 : Proof (at (s 0)) → Proof ("x" ==n (nat 5))
ps0⇒x==5 p = s3=>x==5 (s2=>s3 (s1=>s2 (s0=>s1 p)))


--============================   While-Program   ===============================

{- == The program ==
  s0: x = 0
  s1: cobegin
    s2: x = 1
    □
    s3: while false {
      s4: x = 6
    }
  coend
  s5: x = 5
-}

w0 : Seg (s 0) ("x" :=n (nat 0)) (s 1)
w0 = seg (s 0) ("x" :=n (nat 0)) (s 1)

w2 : Seg (s 2) ("x" :=n (nat 1)) (fin (s 2))
w2 = seg (s 2) ("x" :=n (nat 1)) (fin (s 2))

w4 : Seg (s 4) ("x" :=n (nat 6)) (s 3)
w4 = seg (s 4) ("x" :=n (nat 6)) (s 3)

w3 : Seg (s 3) (while (bool false) (s 4)) (fin (s 3))
w3 = seg (s 3) (while (bool false) (s 4)) (fin (s 3))

w1 : Seg (s 1) ((s 2) || (s 3)) (s 5)
w1 = seg ((s 1)) ((s 2) || (s 3)) (s 5)

w5 : Seg (s 5) ("x" :=n (nat 5)) (fin (s 5))
w5 = seg (s 5) ("x" :=n (nat 5)) (fin (s 5))


-- Termination proof

w0=>w1 : Proof (at (s 0)) → Proof (at (s 1))
w0=>w1 p = flow (∧-e₁ (:=n-R p s0)) w0

w1=>w2∧w3 : Proof (at (s 1)) → Proof (at (s 2) ∧ at (s 3))
w1=>w2∧w3 p = parRule p w1

w2∧w3=>w2'∧w3' : Proof (at (s 2) ∧ at (s 3)) → Proof(after (s 2) ∧ after (s 3))
w2∧w3=>w2'∧w3' p = ∧-i (∧-e₁ (:=n-R (∧-e₁ p) w2)) (exWhile-F (∧-e₂ p) w3)

w2'∧w3'=>s5 : Proof(after (s 2) ∧ after (s 3)) → Proof (at (s 5))
w2'∧w3'=>s5 p = flow (exitPar p w1) w1

s5=>x==5 : Proof (at (s 5)) → Proof ("x" ==n (nat 5))
s5=>x==5 p = ∧-e₂ (:=n-R p w5)

-- Final proof of termination from the entry point.
s0=>x==5 : Proof (at (s 0)) → Proof ("x" ==n (nat 5))
s0=>x==5 p = s5=>x==5 (w2'∧w3'=>s5 (w2∧w3=>w2'∧w3' (w1=>w2∧w3 (w0=>w1 p))))

-- Proof of termination and property of variable "x"
s0=>x==5∧s5' : Proof (at (s 0)) → Proof (("x" ==n (nat 5)) ∧ (after (s 5)))
s0=>x==5∧s5' p = ∧-comm (:=n-R (w2'∧w3'=>s5 (w2∧w3=>w2'∧w3' (w1=>w2∧w3 (w0=>w1 p)))) w5)


--=======================   "Advanced" While Program   =========================

{- == The program ==
  s0: x = true
  s1: cobegin
    s2: x = false
    □
    s3: while x {
      s4: y = 5
    }
  coend
  s5: y = 6
-}

a0 : Seg (s 0) ("x" :=b (bool true)) (s 1)
a0 = seg (s 0) ("x" :=b (bool true)) (s 1)

a1 : Seg (s 1) ((s 2) || (s 3)) (s 5)
a1 = seg ((s 1)) ((s 2) || (s 3)) (s 5)

a2 : Seg (s 2) ("x" :=b (bool false)) (fin (s 2))
a2 = seg (s 2) ("x" :=b (bool false)) (fin (s 2))

a3 : Seg (s 3) (while (var "x") (s 4)) (fin (s 3))
a3 = seg (s 3) (while (var "x") (s 4)) (fin (s 3))

a4 : Seg (s 4) ("y" :=n (nat 5)) (s 3)
a4 = seg (s 4) ("y" :=n (nat 5)) (s 3)

a5 : Seg (s 5) ("y" :=n (nat 6)) (fin (s 5))
a5 = seg (s 5) ("y" :=n (nat 6)) (fin (s 5))


-- Termination Proof

a0=>a2∧a3 : Proof(at (s 0)) → Proof ((at (s 2)) ∧ (at (s 3)))
a0=>a2∧a3 p = parRule (flow (∧-e₁ (:=b-T-R p a0)) a0) a1

a2=>□∼x : Proof (at (s 2)) → Proof (□ (∼ (tr (var "x"))))
a2=>□∼x p = □-∧-e₂ (⇒-e ((custom ((after (s 2)) ∧ (∼ (tr (var "x")))) (□ ((after (s 2)) ∧ (∼ (tr (var "x"))))))) (:=b-F-R p a2))

a2∧a3=>a2'∧a3' : Proof ((at (s 2)) ∧ (at (s 3))) → Proof ((after (s 2)) ∧ (after (s 3)))
a2∧a3=>a2'∧a3' p = ∧-i (∧-e₁ (:=b-F-R (∧-e₁ p) a2)) (exitWhile (∧-i (∧-e₂ p) (a2=>□∼x (∧-e₁ p))) a3)

a2'∧a3'=>a5 : Proof ((after (s 2)) ∧ (after (s 3))) → Proof (at (s 5))
a2'∧a3'=>a5 p = flow (exitPar p a1) a1

-- Final proof of Termination

s0=>s5' : Proof (at (s 0)) → Proof (after (s 5))
s0=>s5' p = ∧-e₁ (:=n-R (a2'∧a3'=>a5 (a2∧a3=>a2'∧a3' (a0=>a2∧a3 p))) a5)
