module DependentWhile where

open import ELTL
open import SatRel
open import Program
open import Data.Bool as Bool using (true; false; Bool)
open import Data.Nat
open import Data.Nat

{- == The program ==
  p0:
    s0: p = true
    s1: q = false
    s2: cobegin
      p1:
        s3: p = false
        s4: while ~ q {
          s5: x = 5
        }
        s6: fin p1
      ||
      p2:
        s7: while p {
          s8: while true {
            s9: x = 6
          }
        }
        s10: q = true
        s11: fin p2
    coend
    s12: x = 1
    s13: fin p0
-}


p0 = proc (prc 0) (s 0)
p1 = proc (prc 1) (s 3)
p2 = proc (prc 2) (s 7)

s0  = seg (s 0)  ("p" :=b (bool true)) (s 1)
s1  = seg (s 1)  ("q" :=b (bool false)) (s 2)
s2  = seg (s 2)  (p1 || p2) (s 12)
s3  = seg (s 3)  ("p" :=b (bool false)) (s 4)
s4  = seg (s 4)  (while ("q" ==b (bool false)) (s 5)) (s 6)
s5  = seg (s 5)  ("x" :=n (nat 5)) (s 4)
s6  = seg (s 6)  (fin p1) (s 6)
s7  = seg (s 7)  (while (var "p") (s 8)) (s 10)
s8  = seg (s 8)  (while (bool false) (s 9)) (s 7)
s9  = seg (s 9)  ("x" :=n (nat 6)) (s 8)
s10 = seg (s 10) ("q" :=b (bool true)) (s 11)
s11 = seg (s 11) (fin p2) (s 11)
s12 = seg (s 12) ("x" :=n (nat 1)) (s 13)
s13 = seg (s 13) (fin p0) (s 13)



-- Proof using regular rules.

s0=>s2 : {pr : Prog p0 0} → pr ⊨ ◇ (at (s 0)) → pr ⊨ ◇ (at (s 2))
s0=>s2 p = :=b-F-step (:=b-T-step (◇-i init) s0) s1

p1=>p1' : {pr : Prog p0 0} → pr ⊨ ◇ (at (prc 1)) → pr ⊨ ◇ (after (prc 1))
p1=>p1' p = fin-R (flow (exitWhile {!   !} {!   !} {! s4  !}) s4) s6


-- Proof method using ~>-rules.

s0~>s2 : {pr : Prog p0 0} → pr ⊨ (at (s 0) ~> at (s 2))
s0~>s2 = ~>-trans (:=b-step' s0) (:=b-step' s1)

ins4~>ats4 : {pr : Prog p0 0} → pr ⊨ (in' (s 4) ~> at (s 4))
ins4~>ats4 = ~>-trans (enterWhile' s4) (:=n-step' s5)

postulate p'~>□p' : {pr : Prog p0 0} → pr ⊨ ((b* ("p" ==b (bool false))) ~> □ (b* ("p" ==b (bool false))))
postulate q'~>□q' : {pr : Prog p0 0} → pr ⊨ ((b* ("q" ==b (bool true))) ~> □ (b* ("q" ==b (bool true))))

ins7~>ats7 : {pr : Prog p0 0} → pr ⊨ (in' (s 7) ~> at (s 7))
ins7~>ats7 = ~>-trans (enterWhile' s7) (~>-trans (exWhile-F' s8) (flow' s8))

s7~>p' : {pr : Prog p0 0} → pr ⊨ (at (s 7) ~> (b* ("p" ==b (bool false))))
s7~>p' = ~>-trans (~>-trans (infPrc' p2) (~>-trans (infPar₁' s2) (enterPrc' p1))) (~>-∧-e₂ (:=b-F-R' s3))

p2~>s10 : {pr : Prog p0 0} → pr ⊨ (at (prc 2) ~> at (s 10))
p2~>s10 = ~>-trans (~>-trans (enterPrc' p2) (exitWhile' (~>-trans s7~>p' p'~>□p') ins7~>ats7 s7)) (flow' s7)

p2~>p2' : {pr : Prog p0 0} → pr ⊨ (at (prc 2) ~> after (prc 2))
p2~>p2' = ~>-trans p2~>s10 (~>-trans (:=b-step' s10) (fin-R' s11))

p1~>q : {pr : Prog p0 0} → pr ⊨ (at (prc 1) ~> (b* ("q" ==b (bool true))))
p1~>q = ~>-trans (infPar₂' s2) (~>-trans p2~>s10 (~>-∧-e₂ (:=b-T-R' s10)))

p1~>p1' : {pr : Prog p0 0} → pr ⊨ (at (prc 1) ~> after (prc 1))
p1~>p1' = ~>-trans (~>-trans (enterPrc' p1) (~>-trans (:=b-step' s3) (~>-trans
  (exitWhileF' (~>-trans (~>-trans (flowInv' s3)
    (~>-trans (infPrc' p1) p1~>q)) q'~>□q') ins4~>ats4 s4) (flow' s4)))) (fin-R' s6)

s2~>s2' : {pr : Prog p0 0} → pr ⊨ (at (s 2) ~> after (s 2))
s2~>s2' = ~>-trans (~>-trans (parRule' s2) (join' s2 p1~>p1' p2~>p2')) (exitPar' s2)

s2'~>x==1 : {pr : Prog p0 0} → pr ⊨ (after (s 2) ~> b* ("x" ==n (nat 1)))
s2'~>x==1 = ~>-trans (flow' s2) (~>-∧-e₂ (:=n-R' s12))

-- Final proof of ◇ x==1

p0⊨◇x==1 : {pr : Prog p0 0} → pr ⊨ ◇ (b* ("x" ==n (nat 1)))
p0⊨◇x==1 = ~>-e (~>-trans s0~>s2 (~>-trans s2~>s2' s2'~>x==1)) (◇-i init)
