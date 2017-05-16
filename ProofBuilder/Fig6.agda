module Fig6 where

open import Program
open import ELTL
open import SatRel
open import Data.Bool as Bool using (Bool; true; false)

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

p0=>s2∧s4 : {pr : Prog p0 0} → pr ⊨ ◇ ((at (s 2)) ∧ (at (s 4)))
p0=>s2∧s4 = parRule (flow (◇-∧-e₁ (:=b-T-R (◇-i init) s0)) s0) s1

s2∧s4=>s2'∧∼x : {pr : Prog p0 0} → pr ⊨ ((◇ ((at (s 2)) ∧ (at (s 4)))) ⇒ (◇ ((after (s 2)) ∧ (∼ (tr (var "p"))))))
s2∧s4=>s2'∧∼x = ⇒-i (:=b-F-R (◇-∧-e₁ assume) s2)

s2'∧∼x=>□s2'∧∼x : {pr : Prog p0 0} → pr ⊨ ((◇ ((after (s 2)) ∧ (∼ (tr (var "p"))))) ⇒ (□ ((after (s 2)) ∧ (∼ (tr (var "p"))))))
s2'∧∼x=>□s2'∧∼x = custom ((◇ ((after (s 2)) ∧ (∼ (tr (var "p")))))) ((□ ((after (s 2)) ∧ (∼ (tr (var "p"))))))

p0=>□s2'∧∼x : {pr : Prog p0 0} → pr ⊨ ◇ ((□ ((after (s 2)) ∧ (∼ (tr (var "p"))))))
p0=>□s2'∧∼x = {!   !}
-- ⇒-e (⇒-trans s2∧s4=>s2'∧∼x s2'∧∼x=>□s2'∧∼x) p0=>s2∧s4

p0=>□is2∨s2' : {pr : Prog p0 0} → pr ⊨ ((◇ (at (s 4))) ⇒ (□ ((in' (s 4)) ∨ (after (s 4)))))
p0=>□is2∨s2' = custom ((◇ (at (s 4)))) (□ (((in' (s 4)) ∨ (after (s 4)))))

ins4=>s4 : {pr : Prog p0 0} → pr ⊨ ◇ (in' (s 4)) → pr ⊨ ◇ (at (s 4))
ins4=>s4 p = ∨-e (in=>at∨inw p s4) assume (flow (◇-∧-e₁ (:=n-R assume s5)) s5)

s4=>s4' :  {pr : Prog p0 0} → pr ⊨ ◇ (at (s 4)) → pr ⊨ ◇ (after (s 4))
s4=>s4' p = exitWhile p {!   !} s4

p0=>s2'∧s3' : {pr : Prog p0 0} → pr ⊨ ◇ ((after (s 2)) ∧ (after (s 4)))
p0=>s2'∧s3' = ∨-e (□-e (⇒-e p0=>□is2∨s2' (◇-∧-e₂ p0=>s2∧s4))) (□-∧-◇ {!   !} {!   !}) (□-∧-◇ (□-∧-e₁ (⇒-e {! s2'∧∼x=>□s2'∧∼x  !} {!   !})) (◇-i assume))
-- ∨-e (⇒-e p0=>□is2∨s2' (◇-∧-e₂ p0=>s2∧s4)) {!   !} (□-∧-◇ (□-∧-e₁ {! s2'∧∼x=>□s2'∧∼x  !}) (◇-i assume))


-- Go through all and check legal state
