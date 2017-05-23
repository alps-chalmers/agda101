module Safety where

open import ELTL
open import SatRel
open import Data.Vec
open import Data.String
open import Data.Nat
open import Data.Bool

data Stm : Set where
  l:_,_:=n_ : (l : String) → (x : String) → (n : ℕ) → Stm
  l:_,_:=b_ : (l : String) → (x : String) → (b : Bool) → Stm

data Proc : ∀ {n} → Vec Stm n → Set where
  proc : ∀ {n} → (v : Vec Stm n) → Proc v

data Program : {n : ℕ} → {v : Vec Stm n} → Proc v → Set where
  program : {n : ℕ} {v : Vec Stm n} → (prc : Proc v) → Program prc

data bot : Set where

record ⊤' : Set where
 tt : ⊤'
 tt = record {}

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
x ∈* proc [] = bot
x ∈* proc (y ∷ v) with x isEq y
... | true = ⊤'
... | false = x ∈* proc v

{-
infSafety : ∀ {n} {v : Vec Stm n} → (s : Stm) → (p : Proc v) → s ∈* p → Set
infSafety stm (proc []) q = ⊤'
infSafety (l: l , x₁ :=n n₁) (proc (x ∷ v)) q = {!   !}
infSafety (l: l , x₁ :=b b) (proc (x ∷ v)) q = {!   !}
-}


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

{-x violates ELTL.T = false
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
x violates b* b = {!   !}-}


infSafety' : ∀ {n} → ELTL → (v : Vec Stm n) → Set
infSafety' φ [] = ⊤'
infSafety' φ (x ∷ v) = if (x violates φ) then bot else (infSafety' φ v)

infSafety : ∀ {n} {v : Vec Stm n} → (φ : ELTL) → (p : Proc v) → infSafety' φ v → ELTL
infSafety φ (proc v) q = □ φ

final : ELTL
final = infSafety (b* ("x" ==n (nat 1))) p0 (record {})
