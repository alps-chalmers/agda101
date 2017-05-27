module Safety where

open import Data.String
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool

data ⊥' : Set where

record T' : Set where
 valid : T'
 valid = record {}

data Block : Set where
  first : String → Block
  _::_  : Block → String → Block

data Stm : Set where
  _:=n_ : (x : String) → (n : ℕ) → Stm
  _:=b_ : (x : String) → (b : Bool) → Stm
  block : (b : Block) → Stm

data Stm* : String → Stm → Set where
  stm   : (l : String) → (st : Stm) → Stm* l st

data Prog : ∀ {l s} → Stm* l s → Set where
  prog : ∀{l s} → (st : Stm* l s) → Prog st

_∈*_ : String → Block → Set
x ∈* first y = if x == y then T' else ⊥'
x ∈* (ys :: y) = if x == y then T' else (x ∈* ys)

_∈_ : ∀ {l₁ l₂ s₁ s₂} {s* : Stm* l₁ s₁} → Stm* l₂ s₂ → Prog s* → Set
stm l₁ st₁ ∈ prog (stm l (block b)) = if (l == l₁) then T' else (l ∈* b)
stm l₁ st₁ ∈ prog (stm l _) = if (l == l₁) then T' else ⊥'

_seq_∈_ : String → String → Block → Set
x seq y ∈ first _ = ⊥'
x seq y ∈ (first x* :: y*) = if ((x == x*) ∧ (y == y*)) then T' else ⊥'
x seq y ∈ ((b :: x*) :: y*) = if ((x == x*) ∧ (y == y*)) then T' else x seq y ∈ b

data ELTL : Set where
  at af : String → ELTL
  ◇     : ELTL → ELTL
  term  : ELTL

fin : Block → String → Set
fin (first x) str = if x == str then T' else ⊥'
fin (b :: x) str = if x == str then T' else ⊥'

data _⊨_ : ∀{l s} {st : Stm* l s} → (p : Prog st) → ELTL → Set where
  -- Program rules
  init        : ∀ {l s} {st : Stm* l s} {p : Prog st} → p ⊨ (at l)
  term        : ∀ {l s} {st : Stm* l s} {p : Prog st} →
    p ⊨ ◇ (af l) → p ⊨ term
  :=n-R       : ∀ {l s l₁ x v} {st : Stm* l s} {p : Prog st} → Stm* l₁ (x :=n v) →
    p ⊨ ◇ (at l₁) → p ⊨ ◇ (af l₁)
  :=b-R       : ∀ {l s l₁ x v} {st : Stm* l s} {p : Prog st} → Stm* l₁ (x :=b v) →
    p ⊨ ◇ (at l₁) → p ⊨ ◇ (af l₁)
  flow        : ∀ {x y l s b bl} {st : Stm* l s} {p : Prog st} → Stm* b (block bl) →
    x seq y ∈ bl → p ⊨ ◇ (af x) → p ⊨ ◇ (at y)
  enterBlock  : ∀ {f l s b bl} {st : Stm* l s} {p : Prog st} →
    (s* : Stm* b (block ((first f) :: bl))) → p ⊨ ◇ (at b) → p ⊨ ◇ (at f)
  exitBlock   : ∀ {l s b bl bl'} {st : Stm* l s} {p : Prog st} →
    (s* : Stm* b (block bl)) → fin bl bl' →
    p ⊨ ◇ (af bl') → p ⊨ ◇ (af b)

  -- LTL Rules
  ◇-i : ∀ {l s φ} {st : Stm* l s} {p : Prog st} → p ⊨ φ → p ⊨ ◇ φ

st : Stm
st = block ((first "s0") :: "s1")

s0 = stm "s0" (block ((first "s1") :: "s2"))
s1 = stm "s1" ("x" :=n 5)
s2 = stm "s2" (block ((first "s3") :: "s4"))
s3 = stm "s3" ("x" :=n 6)
s4 = stm "s4" ("y" :=b true)

p⊨s1 : {p : Prog s0} → p ⊨ ◇ (at "s1")
p⊨s1 = enterBlock s0 (◇-i init)

s1=>s2 : {p : Prog s0} → p ⊨ ◇ (at "s1") → p ⊨ ◇ (at "s2")
s1=>s2 x = flow s0 (record {}) (:=n-R s1 x)

s2=>s4 : {p : Prog s0} → p ⊨ ◇ (at "s2") → p ⊨ ◇ (at "s4")
s2=>s4 x = flow s2 (record {}) (:=n-R s3 (enterBlock s2 x))

s2=>s2' : {p : Prog s0} → p ⊨ ◇ (at "s2") → p ⊨ ◇ (af "s2")
s2=>s2' x = exitBlock s2 (record {}) (:=b-R s4 (s2=>s4 x))

s1=>s0' : {p : Prog s0} → p ⊨ ◇ (at "s1") → p ⊨ ◇ (af "s0")
s1=>s0' x = exitBlock s0 (record {}) (s2=>s2' (s1=>s2 x))

p' : {p : Prog s0} → p ⊨ term
p' = term (s1=>s0' p⊨s1)


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
