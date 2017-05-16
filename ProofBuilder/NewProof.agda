module NewProof where

open import ELTL
open import SatRel
open import Program
open import Data.Bool as Bool using (true; false; Bool)
open import Data.Nat

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
          s5: y = 1
        }
        s6: fin p2
    coend
    s7: fin p0
-}

p0 = proc (prc 0) (s 0)
p1 = proc (prc 1) (s 2)
p2 = proc (prc 2) (s 4)

s0 = seg (s 0) ("p" :=b (bool true)) (s 1)
s1 = seg (s 1) (p1 || p2) (s 7)
s2 = seg (s 2) ("p" :=b (bool false)) (s 3)
s3 = seg (s 3) (fin p1) (s 3)
s4 = seg (s 4) (while (var "p") (s 5)) (s 6)
s5 = seg (s 5) ("y" :=n (nat 1)) (s 4)
s6 = seg (s 6) (fin p2) (s 6)
s7 = seg (s 7) (fin p0) (s 7)


s0=>s1 : {pr : Prog p0 0} → pr ⊨ ((at (s 0)) ~> (at (s 1)))
s0=>s1 = ~>-trans (<:=b>-flow s0) (flow' s0)

s1=>s2 : {pr : Prog p0 0} → pr ⊨ ((at (s 1)) ~> (at (s 2)))
s1=>s2 = ~>-∧-e₁ (parRule' s1)

s1=>s4 : {pr : Prog p0 0} → pr ⊨ ((at (s 1)) ~> (at (s 4)))
s1=>s4 = ~>-∧-e₂ (parRule' s1)

s2=>p1' : {pr : Prog p0 0} → pr ⊨ ((at (s 2)) ~> (after (prc 1)))
s2=>p1' = ~>-trans (~>-trans (<:=b>-flow s2) (~>-trans (flow' s2) ~>-refl)) (fin-R' s3)

p1=>□p1' : {pr : Prog p0 0} → pr ⊨ ((after (prc 1)) ~> (□ (after (prc 1))))
p1=>□p1' = custom (after (prc 1)) (□ (after (prc 1)))

s4=>s4' : {pr : Prog p0 0} → pr ⊨ ((at (s 4)) ~> (after (s 4)))
s4=>s4' = {! exitWhile'  !}
--  ~>-trans {!   !} (exitWhile' s4)

s4'=>p2' : {pr : Prog p0 0} → pr ⊨ ((after (s 4)) ~> (after (prc 2)))
s4'=>p2' = ~>-trans (flow' s4) (fin-R' s6)

p2=>□p2' : {pr : Prog p0 0} → pr ⊨ ((after (prc 2)) ~> (□ (after (prc 2))))
p2=>□p2' = custom (after (prc 2)) (□ (after (prc 2)))

s1=>s1' : {pr : Prog p0 0} → pr ⊨ ((at (s 1)) ~> (after (s 1)))
s1=>s1' = ~>-trans {!   !} (exitPar' s1)


p0=>s1 : {pr : Prog p0 0} → pr ⊨ ◇ (at (s 4))
p0=>s1 = ~>-e (~>-trans s0=>s1 s1=>s4) (◇-i init)
 -- ~>-e s0=>s1 (◇-i init)
