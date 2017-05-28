module Safety where

open import Data.String
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import ELTL
open import CPL
open import SatRel

{-
s0: {
  s1: x = 5
  s2: {
    s3: x = 6
    s4: par {
      s5: x = 1
      ||
      s6: x = 2
    }
  }
}
-}

{-
s0 = stm "s0" (block ((first "s1") :: "s2"))
s1 = stm "s1" ("x" :=n (nat 5))
s2 = stm "s2" (block ((first "s3") :: "s4"))
s3 = stm "s3" ("x" :=n (nat 6))
s4 = stm "s4" ("s5" || "s6")
s5 = stm "s5" (("x" :=n (nat 1)))
s6 = stm "s6" (("x" :=n (nat 2)))

p⊨s1 : {p : Prog s0 0} → p ⊨ ◇ (at "s1")
p⊨s1 = enterBlock s0 (◇-i init)

s1=>s2 : {p : Prog s0 0} → p ⊨ ◇ (at "s1") → p ⊨ ◇ (at "s2")
s1=>s2 x = flow s0 (record {}) (:=n-step s1 x)

s2=>s4 : {p : Prog s0 0} → p ⊨ ◇ (at "s2") → p ⊨ ◇ (at "s4")
s2=>s4 x = flow s2 (record {}) (:=n-step s3 (enterBlock s2 x))

s4=>s4' : {p : Prog s0 0} → p ⊨ ◇ (at "s4") → p ⊨ ◇ (af "s4")
s4=>s4' x = exitPar s4 (join s4 (:=n-step s5 (◇-∧-e₁ (enterPar s4 x))) (:=n-step s6 (◇-∧-e₂ (enterPar s4 x))))

s4=>s2' : {p : Prog s0 0} → p ⊨ ◇ (at "s4") → p ⊨ ◇ (af "s2")
s4=>s2' x = exitBlock s2 (record {}) (s4=>s4' x)

s1=>s0' : {p : Prog s0 0} → p ⊨ ◇ (at "s1") → p ⊨ ◇ (af "s0")
s1=>s0' x = exitBlock s0 (record {}) (s4=>s2' (s2=>s4 (s1=>s2 (enterBlock s0 (◇-i init)))))

p' : {p : Prog s0 0} → p ⊨ term
p' = term (s1=>s0' p⊨s1)
-}

-- exitBlock s0 (record {}) axi

-- test : ∀{l v} → Stm* l (block v) → String
-- test {v} st = head {! v  !}
{-
s0 : Stm
s0 = l: "s0" , "x" :=n 1
s1 : Stm
s1 = l: "s1" , "x" :=n 1
s2 : Stm
s2 = l: "s2" , "x" :=n 1
s3 : Stm
s3 = l: "s3" , "x" :=b false

vec  = (s0 ∷ s1 ∷ s2 ∷ s3 ∷ [])
p0 = proc vec

_isEq_ : Stm → Stm → Bool
(l: x , x₁ :=n x₂) isEq (l: x₃ , x₄ :=n x₅) = x == x₃
(l: x , x₁ :=b x₂) isEq (l: x₃ , x₄ :=n x₅) = x == x₃
_ isEq _ = false

_∈*_ : ∀ {n} {v : Vec Stm n} → (s : Stm) → Proc v → Set
x ∈* proc [] = ⊥'
x ∈* proc (y ∷ v) with x isEq y
... | true = T'
... | false = x ∈* proc v
-}
{-
infSafety : ∀ {n} {v : Vec Stm n} → (s : Stm) → (p : Proc v) → s ∈* p → Set
infSafety stm (proc []) q = T'
infSafety (l: l , x₁ :=n n₁) (proc (x ∷ v)) q = {!   !}
infSafety (l: l , x₁ :=b b) (proc (x ∷ v)) q = {!   !}
-}

{-
_eq_ : ℕ → ℕ → Bool
zero eq zero = true
suc y eq zero = false
zero eq suc y = false
suc x eq suc y = x eq y

-- TODO
-- If □, then check violates

_violates_ : Stm → ELTL → Bool
(l: l , x :=n n) violates (b* ("x" ==n (nat y))) = not (n eq y)
(l: l , x :=b b) violates (b* ("x" ==b (bool b'))) = not (b Data.Bool.∧ b')
_ violates _ = false

x violates ELTL.T = false
x violates ⊥ = true
x violates ∼ y = not (x violates y)
x violates □ y = x violates y
x violates ◇ y = {!   !}
x violates (y ELTL.∧ y₁) = {!   !}
x violates (y ELTL.∨ y₁) = {!   !}
x violates (y ⇒ y₁) = {!   !}
x violates (y ~> y₁) = {!   !}
x violates at l = {!   !}
x violates in' l = {!   !}
x violates after l = {!   !}
x violates b* b = {!   !}


infSafety' : ∀ {n} → ELTL → (v : Vec Stm n) → Set
infSafety' φ [] = T'
infSafety' φ (x ∷ v) = if (x violates φ) then ⊥' else (infSafety' φ v)

infSafety : ∀ {n} {v : Vec Stm n} → (φ : ELTL) → (p : Proc v) → infSafety' φ v → ELTL
infSafety φ (proc v) q = □ φ

final : ELTL
final = infSafety (b* ("x" ==n (nat 1))) p0 (record {})
-}
