module ProofBuilder where

open import LTLRules
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


-- Termination proof for the program.

p0=>s1 : ∀{n} {p : Prog (s 0) n} → p ⊨ (at (s 1))
p0=>s1 {n} {p} = flow (∧-e₁ (:=n-R (init p) s0)) s0

p0=>s2 : ∀{n} {p : Prog (s 0) n} → p ⊨ (at (s 2))
p0=>s2 = flow (∧-e₁ (:=n-R p0=>s1 s1)) s1

p0=>s3∧s4 : ∀{n} {p : Prog (s 0) n} → p ⊨ ((at (s 3)) ∧ (at (s 4)))
p0=>s3∧s4 = parRule p0=>s2 s2

p0=>s3' : ∀{n} {p : Prog (s 0) n} → p ⊨ (after (s 3))
p0=>s3' = ∧-e₁ (:=n-R (∧-e₁ p0=>s3∧s4) s3)

p0=>s4' : ∀{n} {p : Prog (s 0) n} → p ⊨ (after (s 4))
p0=>s4' = ∧-e₁ (:=n-R (∧-e₂ p0=>s3∧s4) s4)

-- Final proof of termination
p0=>s2' : ∀{n} {p : Prog (s 0) n} → p ⊨ (after (s 2))
p0=>s2' = exitPar (∧-i p0=>s3' p0=>s4') s2

-- Proof of ◇ x==5
p0=>x==5 : ∀{n} {p : Prog (s 0) n} → p ⊨ ("x" ==n (nat 5))
p0=>x==5 = ∧-e₂ (:=n-R (∧-e₁ p0=>s3∧s4) s3)


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

w0=>w1 : ∀{n} {p : Prog (s 0) n} → p ⊨ (at (s 1))
w0=>w1 {n} {p} = flow (∧-e₁ (:=n-R (init p) w0)) w0

w1=>w2∧w3 : ∀{n} {p : Prog (s 0) n} → p ⊨ (at (s 1)) → p ⊨ ((at (s 2)) ∧ (at (s 3)))
w1=>w2∧w3 p = parRule p w1

w2∧w3=>w2'∧w3' : ∀{n} {p : Prog (s 0) n} → p ⊨ ((at (s 2)) ∧ (at (s 3))) → p ⊨ ((after (s 2)) ∧ (after (s 3)))
w2∧w3=>w2'∧w3' p = ∧-i (∧-e₁ (:=n-R (∧-e₁ p) w2)) (exWhile-F (∧-e₂ p) w3)

w2'∧w3'=>w5 : ∀{n} {p : Prog (s 0) n} → p ⊨ ((after (s 2)) ∧ (after (s 3))) → p ⊨ (at (s 5))
w2'∧w3'=>w5 p = flow (exitPar (w2∧w3=>w2'∧w3' (w1=>w2∧w3 w0=>w1)) w1) w1

w5=>w5' : ∀{n} {p : Prog (s 0) n} → p ⊨ (at (s 5)) → p ⊨ (after (s 5))
w5=>w5' p = ∧-e₁ (:=n-R (w2'∧w3'=>w5 (w2∧w3=>w2'∧w3' (w1=>w2∧w3 w0=>w1))) w5)

-- Proof of termination and property of variable "x"
s0=>x==5∧s5' : ∀{n} {p : Prog (s 0) n} → p ⊨ (at (s 0)) → p ⊨ (("x" ==n (nat 5)) ∧ (after (s 5)))
s0=>x==5∧s5' p = ∧-comm (:=n-R (w2'∧w3'=>w5 (w2∧w3=>w2'∧w3' (w1=>w2∧w3 w0=>w1))) w5)


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


-- Termination proof


p=>a2∧a3 : ∀{n} {p : Prog (s 0) n} → p ⊨ ((at (s 2)) ∧ (at (s 3)))
p=>a2∧a3 {n} {p} = parRule (flow (∧-e₁ (:=b-T-R (init p) a0)) a0) a1

a2=>□~x : ∀{n} {p : Prog (s 0) n} → p ⊨ (□ (∼ (tr (var "x"))))
a2=>□~x = □-∧-e₂ (custom (((after (s 2)) ∧ (∼ (tr (var "x"))))) ((□ ((after (s 2)) ∧ ∼ (tr (var "x"))))) ((:=b-F-R (∧-e₁ p=>a2∧a3) a2)))

p=>a2'∧a3' : ∀{n} {p : Prog (s 0) n} → p ⊨ ((after (s 2)) ∧ (after (s 3)))
p=>a2'∧a3' = ∧-i (∧-e₁ (:=b-F-R (∧-e₁ p=>a2∧a3) a2)) (exitWhile (∧-i (∧-e₂ p=>a2∧a3) a2=>□~x) a3)

p=>a1' : ∀{n} {p : Prog (s 0) n} → p ⊨ (after (s 1))
p=>a1' = exitPar p=>a2'∧a3' a1

-- Final proof of Termination

p=>x==6∧a5' : ∀{n} {p : Prog (s 0) n} → p ⊨ (("x" ==n (nat 6)) ∧ (after (s 5)))
p=>x==6∧a5' = ∧-comm (:=n-R (flow p=>a1' a1) a5)
