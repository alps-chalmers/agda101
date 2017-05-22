module ProofBuilder where

open import SatRel
open import Program
open import ELTL
open import Data.Bool as Bool using (Bool; true; false)

-- TODO
-- * Index Label over ℕ

--============================   Simple Program   ==============================

{-
  p0:
    s0: x = 0
    s1: x = 1
    s2: cobegin
      p1:
        s3: x = 5
        s4: fin p1
      □
      p2:
        s5: x = 6
        s6 : fin p2
    coend
    s7: fin p0
-}

-- Program representation --

p0 = proc (prc 0) (s 0)
p1 = proc (prc 1) (s 3)
p2 = proc (prc 2) (s 5)

s0 = seg (s 0) ("x" :=n (nat 0)) (s 1)
s1 = seg (s 1) ("x" :=n (nat 1)) (s 2)
s2 = seg (s 2) (p1 || p2) (s 7)
s3 = seg (s 3) ("x" :=n (nat 5)) (s 4)
s4 = seg (s 4) (fin p1) (s 4)
s5 = seg (s 5) ("x" :=n (nat 6)) (s 6)
s6 = seg (s 6) (fin p2) (s 6)
s7 = seg (s 7) (fin p0) (s 7)

-- Termination lemmas.

p0=>s1 : {pr : Prog p0 0} → pr ⊨ ◇ (at (s 1))
p0=>s1 = flow (◇-∧-e₁ (:=n-R (◇-i init) s0)) s0

p0=>s2 : {pr : Prog p0 0} → pr ⊨ ◇ (at (s 2))
p0=>s2 = flow (◇-∧-e₁ (:=n-R p0=>s1 s1)) s1

p0=>s3∧s5 : {pr : Prog p0 0} → pr ⊨ ◇ ((at (s 3)) ∧ (at (s 5)))
p0=>s3∧s5 = parRule p0=>s2 s2

p0=>s3' : {pr : Prog p0 0} → pr ⊨ ◇ (after (s 3))
p0=>s3' = ◇-∧-e₁ (:=n-R (◇-∧-e₁ p0=>s3∧s5) s3)

p0=>p1' : {pr : Prog p0 0} → pr ⊨ ◇ (after (prc 1))
p0=>p1' = fin-R (flow p0=>s3' s3) s4

p0=>s5' : {pr : Prog p0 0} → pr ⊨ ◇ (after (s 5))
p0=>s5' = ◇-∧-e₁ (:=n-R (◇-∧-e₂ p0=>s3∧s5) s5)

p0=>p2' : {pr : Prog p0 0} → pr ⊨ ◇ (after (prc 2))
p0=>p2' = fin-R (flow p0=>s5' s5) s6

p0=>s7 : {pr : Prog p0 0} → pr ⊨ ◇ (at (s 7))
p0=>s7 = flow (exitPar p0=>p1' p0=>p2' s2) s2

-- Proof of termination.

p0=>p0' : {pr : Prog p0 0} → pr ⊨ ◇ (after (prc 0))
p0=>p0' = fin-R p0=>s7 s7

-- Showcase of branching using assumptions.

s0∨s1=>s1' : {pr : Prog p0 0} → pr ⊨ ((((◇ (at (s 0))) ∨ (◇ (at (s 1))))) ⇒ (◇ (after (s 1))))
s0∨s1=>s1' = ⇒-i (∨-e assume ((◇-∧-e₁ (:=n-R (flow (◇-∧-e₁ (:=n-R assume s0)) s0) s1))) ((◇-∧-e₁ (:=n-R assume s1))))

--============================   While-Program   ===============================

{- == The program ==
  p0:
    s0: x = 0
    s1: cobegin
      p1:
        s2: x = 1
        s3: fin p1
      □
      p2:
        s4: while false {
          s5: x = 6
        }
        s6: fin p2
    coend
    s7: x = 5
    s8: fin p0
-}

-- Program representation

pw0 = proc (prc 0) (s 0)
pw1 = proc (prc 1) (s 2)
pw2 = proc (prc 2) (s 4)

w0 = seg (s 0) ("x" :=n (nat 0)) (s 1)
w1 = seg (s 1) (pw1 || pw2) (s 7)
w2 = seg (s 2) ("x" :=n (nat 1)) (s 3)
w3 = seg (s 3) (fin pw1) (s 3)
w4 = seg (s 4) (while (bool false) (s 5)) (s 6)
w5 = seg (s 5) ("x" :=n (nat 6)) (s 3)
w6 = seg (s 6) (fin pw2) (s 6)
w7 = seg (s 7) ("x" :=n (nat 5)) (s 8)
w8 = seg (s 8) (fin pw0) (s 8)

-- Termination lemmas

pw0=>w2∧w4 : {pr : Prog pw0 0} → pr ⊨ ◇ ((at (s 2)) ∧ (at (s 4)))
pw0=>w2∧w4 = parRule (flow (◇-∧-e₁ (:=n-R (◇-i init) w0)) w0) w1

w2=>pw1' : {pr : Prog pw0 0} → pr ⊨ ◇ (at (s 2)) → pr ⊨ ◇ (after (prc 1))
w2=>pw1' p = fin-R (flow (◇-∧-e₁ (:=n-R p w2)) w2) w3

w4=>pw2' : {pr : Prog pw0 0} → pr ⊨ ◇ (at (s 4)) → pr ⊨ ◇ (after (prc 2))
w4=>pw2' p = fin-R (flow (exWhile-F p w4) w4) w6

pw0=>w7 : {pr : Prog pw0 0} → pr ⊨ ◇ (at (s 7))
pw0=>w7 = flow (exitPar (w2=>pw1' (◇-∧-e₁ pw0=>w2∧w4)) (w4=>pw2' (◇-∧-e₂ pw0=>w2∧w4)) w1) w1

-- Proof of termination

pw0=>pw0' : {pr : Prog pw0 0} → pr ⊨ ◇ (after (prc 0))
pw0=>pw0' = fin-R (flow (◇-∧-e₁ (:=n-R pw0=>w7 w7)) w7) w8

-- Termination using ~>

w0~>p1∧p2 : {pr : Prog pw0 0} → pr ⊨ (at (s 0) ~> (at (prc 1) ∧ at (prc 2)))
w0~>p1∧p2 = ~>-trans (:=n-step w0) (parRule' w1)

p1~>p1' : {pr : Prog pw0 0} → pr ⊨ (at (prc 1) ~> after (prc 1))
p1~>p1' = ~>-trans (enterPrc pw1) (~>-trans (:=n-step w2) (fin-R' w3))

p2~>p2' : {pr : Prog pw0 0} → pr ⊨ (at (prc 2) ~> after (prc 2))
p2~>p2' = ~>-trans (~>-trans (~>-trans (enterPrc pw2) (exWhile-F' w4)) (flow' w4)) (fin-R' w6)

p1∧p2~>p1'∧p2' : {pr : Prog pw0 0} → pr ⊨ ((at (prc 1) ∧ at (prc 2)) ~> (after (prc 1) ∧ after (prc 2)))
p1∧p2~>p1'∧p2' = join w1 p1~>p1' p2~>p2'

p1'∧p2'~>w7 : {pr : Prog pw0 0} → pr ⊨ ((after (prc 1) ∧ after (prc 2)) ~> at (s 7))
p1'∧p2'~>w7 = ~>-trans (exitPar' w1) (flow' w1)

w7~>p0' : {pr : Prog pw0 0} → pr ⊨ (at (s 7) ~> after (prc 0))
w7~>p0' = ~>-trans (:=n-step w7) (fin-R' w8)

-- Proof of termination

p0⇒p0' : {pr : Prog pw0 0} → pr ⊨ ◇ (after (prc 0))
p0⇒p0' = ~>-e (~>-trans (~>-trans (~>-trans w0~>p1∧p2 p1∧p2~>p1'∧p2') p1'∧p2'~>w7) w7~>p0') (◇-i init)

--=======================   "Advanced" While Program   =========================

{- == The program ==
  p0:
    s0: x = true
    s1: cobegin
      p1:
        s2: x = false
        s3: fin p1
      □
      p2:
        s4: while x {
          s5: y = 5
        }
        s6: fin p2
    coend
    s7: y = 6
    s8: fin p0
-}

-- Program representation

pa0 = proc (prc 0) (s 0)
pa1 = proc (prc 1) (s 2)
pa2 = proc (prc 2) (s 4)

a0 = seg (s 0) ("x" :=b (bool true)) (s 1)
a1 = seg (s 1) (pa1 || pa2) (s 7)
a2 = seg (s 2) ("x" :=b (bool false)) (s 3)
a3 = seg (s 3) (fin pw1) (s 3)
a4 = seg (s 4) (while (var "x") (s 5)) (s 6)
a5 = seg (s 5) ("y" :=n (nat 5)) (s 3)
a6 = seg (s 6) (fin pw2) (s 6)
a7 = seg (s 7) ("y" :=n (nat 6)) (s 8)
a8 = seg (s 8) (fin pw0) (s 8)


-- Termination lemmas

pa0=>a2∧a4 : {pr : Prog pa0 0} → pr ⊨ ◇ ((at (s 2)) ∧ (at (s 4)))
pa0=>a2∧a4 = parRule (flow (◇-∧-e₁ (:=b-T-R (◇-i init) a0)) w0) w1

a2=>pa1' : {pr : Prog pa0 0} → pr ⊨ ◇ (at (s 2)) → pr ⊨ ◇ (after (prc 1))
a2=>pa1' p = fin-R (flow (◇-∧-e₁ (:=b-F-R p a2)) a2) a3

-- Should be checked by SafetyChecker
postulate ∼x=>□∼x : {pr : Prog pa0 0} → pr ⊨ ◇ (b* ("x" ==b (bool false))) → pr ⊨ ◇ (□ (b* ("x" ==b (bool false))))
a4=>a4' : {pr : Prog pa0 0} → pr ⊨ ◇ (at (s 4)) → pr ⊨ ◇ (after (s 4))
a4=>a4' p = exitWhile p (∼x=>□∼x (◇-∧-e₂ (:=b-F-R (◇-∧-e₁ pa0=>a2∧a4) a2))) a4

a4=>pa2' : {pr : Prog pa0 0} → pr ⊨ ◇ (at (s 4)) → pr ⊨ ◇ (after (prc 2))
a4=>pa2' p = fin-R (flow (a4=>a4' p) a4) a6

pa0=>s7 : {pr : Prog pa0 0} → pr ⊨ ◇ (at (s 7))
pa0=>s7 = flow (exitPar (a2=>pa1' (◇-∧-e₁ pa0=>a2∧a4)) (a4=>pa2' (◇-∧-e₂ pa0=>a2∧a4)) a1) a1

-- Proof of termination

pa0=>pa0' : {pr : Prog pa0 0} → pr ⊨ ◇ (after (prc 0))
pa0=>pa0' = fin-R (flow (◇-∧-e₁ (:=n-R pa0=>s7 a7)) a7) a8
