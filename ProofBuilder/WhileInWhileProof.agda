module WhileInWhileProof where

open import ELTL
open import SatRel
open import Program
open import Data.Bool as Bool using (true; false; Bool)
open import Data.Nat


-- Example proof that demonstrates that you cannot exit loops if trere are
-- impassable statements within.

--=========================== Example of while true ==========================--

{- == The program ==
  p0:
    s0: x = true
    s1: cobegin
      p1:
        s2: p = false
        s3: fin p1
      □
      p2:
        s4: while p {
          s5: x = 5
          s6: while true {
            s7: x = 6
          }
        }
        s8: fin p2
    coend
    s9: fin p0
-}

p0 = proc (prc 0) (s 0)
p1 = proc (prc 1) (s 2)
p2 = proc (prc 2) (s 4)

s0 = seg (s 0) ("p" :=b (bool true)) (s 1)
s1 = seg (s 1) (p1 || p2) (s 7)
s2 = seg (s 2) ("p" :=b (bool false)) (s 3)
s3 = seg (s 3) (fin p1) (s 3)
s4 = seg (s 4) (while (var "p") (s 5)) (s 6)
s5 = seg (s 5) ("y" :=n (nat 1)) (s 6)
s6 = seg (s 6) (while (bool true) (s 7)) (s 4)
s7 = seg (s 7) ("x" :=n (nat 6)) (s 6)
s8 = seg (s 8) (fin p2) (s 8)
s9 = seg (s 9) (fin p0) (s 9)

p0~>s1 : {pr : Prog p0 0} → pr ⊨ (at (prc 0) ~> at (s 1))
p0~>s1 = ~>-trans (enterPrc p0) (:=b-step s0)

s1~>s2 : {pr : Prog p0 0} → pr ⊨ (at (s 1) ~> at (s 2))
s1~>s2 = ~>-trans (~>-∧-e₁ (parRule' s1)) (enterPrc p1)

s1~>s4 : {pr : Prog p0 0} → pr ⊨ (at (s 1) ~> at (s 4))
s1~>s4 = ~>-trans (~>-∧-e₂ (parRule' s1)) (enterPrc p2)

postulate p'~>□p' : {pr : Prog p0 0} → pr ⊨ ((b* ("p" ==b (bool false))) ~> □ (b* ("p" ==b (bool false))))

s2~>□p' : {pr : Prog p0 0} → pr ⊨ (at (s 2) ~> □ (b* ("p" ==b (bool false))))
s2~>□p' = ~>-trans (~>-∧-e₂ (:=b-F-R' s2)) p'~>□p'


-- The proof gets stuck here, since there is no way of getting out of the while true.
-- The "?" requires a proof of pr ⊨ at s6 ~> after s6, which there is no rule for.
{-
s4~>s4' : {pr : Prog p0 0} → pr ⊨ (at (s 4) ~> after (s 4))
s4~>s4' = exitWhile' (~>-trans (infPrc p2) (~>-trans (infPar₁ s1) (~>-trans (enterPrc p1) s2~>□p')))
  (~>-trans (~>-trans (enterWhile s4) (:=n-step s5)) (~>-trans ? (flow' s6))) s4
-}


--========================== Example of while false ==========================--

-- This is the exact same program, but with a while false instead.
-- Below is the proof of pr ⊨ ◇ (after s4).

p0* = proc (prc 0) (s 0)
p1* = proc (prc 1) (s 2)
p2* = proc (prc 2) (s 4)

l0 = seg (s 0) ("p" :=b (bool true)) (s 1)
l1 = seg (s 1) (p1 || p2) (s 7)
l2 = seg (s 2) ("p" :=b (bool false)) (s 3)
l3 = seg (s 3) (fin p1) (s 3)
l4 = seg (s 4) (while (var "p") (s 5)) (s 6)
l5 = seg (s 5) ("y" :=n (nat 1)) (s 6)
l6 = seg (s 6) (while (bool false) (s 7)) (s 4)
l7 = seg (s 7) ("x" :=n (nat 6)) (s 6)
l8 = seg (s 8) (fin p2) (s 8)
l9 = seg (s 9) (fin p0) (s 9)

s1~>l4 : {pr : Prog p0 0} → pr ⊨ (at (s 1) ~> at (s 4))
s1~>l4 = ~>-trans (~>-∧-e₂ (parRule' s1)) (enterPrc p2)

postulate p*'~>□p*' : {pr : Prog p0 0} → pr ⊨ ((b* ("p" ==b (bool false))) ~> □ (b* ("p" ==b (bool false))))

l2~>□p' : {pr : Prog p0 0} → pr ⊨ (at (s 2) ~> □ (b* ("p" ==b (bool false))))
l2~>□p' = ~>-trans (~>-∧-e₂ (:=b-F-R' s2)) p*'~>□p*'

l4~>l4' : {pr : Prog p0 0} → pr ⊨ (at (s 4) ~> after (s 4))
l4~>l4' = exitWhile' (~>-trans (infPrc p2) (~>-trans (infPar₁ s1) (~>-trans (enterPrc p1) s2~>□p')))
  (~>-trans (~>-trans (enterWhile s4) (:=n-step s5)) (~>-trans (exWhile-F' l6) (flow' s6))) s4

-- Proof of pr ⊨ ◇ (after s4).
p⊨◇s4' : {pr : Prog p0 0} → pr ⊨ ◇ (after (s 4))
p⊨◇s4' = ~>-e (~>-trans (~>-trans (:=b-step l0) s1~>l4) l4~>l4') (◇-i init)
