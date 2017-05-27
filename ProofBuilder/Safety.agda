module Safety where

open import Data.String
open import Data.Nat
open import Data.Nat.Show
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)

infixl 6 T ⊥ _==n_ _==b_ at in' af
infixl 7 □ ◇
infixl 8 ∼
infixl 9 _∨_ _∧_
infixl 10 _⇒_ _~>_

-- ℕ extended with variables.
data ℕ* : Set where
  nat  : (n : ℕ) → ℕ*
  var  : (x : String) → ℕ*
  _+*_ : (n₁ n₂ : ℕ*) → ℕ*
  _-*_ : (n₁ n₂ : ℕ*) → ℕ*
  _×*_ : (n₁ n₂ : ℕ*) → ℕ*

-- Bool extended with variables.
data Bool* : Set where
  var   : (x : String) → Bool*
  bool  : (b : Bool) → Bool*
  _<*_  : (x : ℕ*) → (y : ℕ*) → Bool*
  _<=*_ : (x : ℕ*) → (y : ℕ*) → Bool*
  _>*_  : (x : ℕ*) → (y : ℕ*) → Bool*
  _>=*_ : (x : ℕ*) → (y : ℕ*) → Bool*
  _==n_ : (x : String) → (n : ℕ*) → Bool*     -- Nat variable x has the value n
  _==b_ : (x : String) → (b : Bool*) → Bool*  -- Bool variable x has the value of y

-- The extended ELTL data type
data ELTL : Set where
  T ⊥           : ELTL                               -- true & false
  ∼             : (φ : ELTL) → ELTL                  -- not
  □ ◇           : (φ : ELTL) → ELTL                  -- always & eventually
  _∧_ _∨_       : (φ : ELTL) → ELTL → ELTL           -- and & or
  _⇒_           : (φ : ELTL) → ELTL → ELTL           -- implies
  _~>_          : (φ : ELTL) → (ψ : ELTL) → ELTL     -- leads to - (P ~> Q) ≡ □(P ⊂ ◇Q)
  at in' af     : (l : String) → ELTL                 -- at, in & after a code segment - extended
  b*            : (b : Bool*) → ELTL
  term          : ELTL

data ⊥' : Set where

record T' : Set where
 valid : T'
 valid = record {}

data Block : Set where
  first : String → Block
  _::_  : Block → String → Block

data Stm : Set where
  _:=n_ : (x : String)  → (n : ℕ*)      → Stm
  _:=b_ : (x : String)  → (b : Bool*)   → Stm
  block : (b : Block)                   → Stm
  _||_  : (s₁ : String) → (s₂ : String) → Stm   -- a and b exectued in parallel
  if    : (b : Bool*)   → (l : String)  → Stm   -- if-statement
  while : (b : Bool*)   → (l : String)  → Stm   -- while-statement
  swapN : (x : String)  → (y : String)  → Stm
  swapB : (x : String)  → (y : String)  → Stm

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
x seq y ∈ (first x* :: y*) = if ((x == x*) Bool.∧ (y == y*)) then T' else ⊥'
x seq y ∈ ((b :: x*) :: y*) = if ((x == x*) Bool.∧ (y == y*)) then T' else x seq y ∈ b

fin : Block → String → Set
fin (first x) str = if x == str then T' else ⊥'
fin (b :: x) str = if x == str then T' else ⊥'

data _⊨_ : ∀{l s} {st : Stm* l s} → (p : Prog st) → ELTL → Set where
  -- Program rules
  init        : ∀ {l s} {st : Stm* l s} {p : Prog st} → p ⊨ (at l)
  term        : ∀ {l s} {st : Stm* l s} {p : Prog st} →
    p ⊨ ◇ (af l) → p ⊨ term
  :=n-R       : ∀ {l s l₁ x v} {st : Stm* l s} {p : Prog st} → Stm* l₁ (x :=n v) →
    p ⊨ ◇ (at l₁) → p ⊨ ◇ (af l₁ ∧ (b* (x ==n v)))
  :=b-R       : ∀ {l s l₁ x v} {st : Stm* l s} {p : Prog st} → Stm* l₁ (x :=b v) →
    p ⊨ ◇ (at l₁) → p ⊨ ◇ (af l₁)
  flow        : ∀ {x y l s b bl} {st : Stm* l s} {p : Prog st} → Stm* b (block bl) →
    x seq y ∈ bl → p ⊨ ◇ (af x) → p ⊨ ◇ (at y)
  enterBlock  : ∀ {f l s b bl} {st : Stm* l s} {p : Prog st} →
    (s* : Stm* b (block ((first f) :: bl))) → p ⊨ ◇ (at b) → p ⊨ ◇ (at f)
  exitBlock   : ∀ {l s b bl bl'} {st : Stm* l s} {p : Prog st} →
    (s* : Stm* b (block bl)) → fin bl bl' →
    p ⊨ ◇ (af bl') → p ⊨ ◇ (af b)
  enterPar    : ∀ {m s l s₁ s₂} {st : Stm* m s} {p : Prog st} → (s* : Stm* l (s₁ || s₂)) →
    p ⊨ ◇ (at l) → p ⊨ ◇ (at s₁ ∧ at s₂)
  exitPar     : ∀ {m s l s₁ s₂} {st : Stm* m s} {p : Prog st} → (s* : Stm* l (s₁ || s₂)) →
    p ⊨ ◇ (af s₁ ∧ af s₂) → p ⊨ ◇ (af l)
  join        : ∀ {m s l s₁ s₂} {st : Stm* m s} {p : Prog st} → (s* : Stm* l (s₁ || s₂)) →
    p ⊨ ◇ (af s₁) → p ⊨ ◇ (af s₂) → p ⊨ ◇ (af s₁ ∧ af s₂)

  -- LTL Rules
  ◇-i : ∀ {l s φ} {st : Stm* l s} {p : Prog st} → p ⊨ φ → p ⊨ ◇ φ
  ◇-∧-e₁ : ∀ {l s φ ψ} {st : Stm* l s} {p : Prog st} → p ⊨ ◇ (φ ∧ ψ) → p ⊨ ◇ φ
  ◇-∧-e₂ : ∀ {l s φ ψ} {st : Stm* l s} {p : Prog st} → p ⊨ ◇ (φ ∧ ψ) → p ⊨ ◇ ψ




:=n-step : ∀ {l s l₁ x v} {st : Stm* l s} {p : Prog st} → Stm* l₁ (x :=n v) →
  p ⊨ ◇ (at l₁) → p ⊨ ◇ (af l₁)
:=n-step st x = ◇-∧-e₁ (:=n-R st x)

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


s0 = stm "s0" (block ((first "s1") :: "s2"))
s1 = stm "s1" ("x" :=n (nat 5))
s2 = stm "s2" (block ((first "s3") :: "s4"))
s3 = stm "s3" ("x" :=n (nat 6))
s4 = stm "s4" ("s5" || "s6")
s5 = stm "s5" (("x" :=n (nat 1)))
s6 = stm "s6" (("x" :=n (nat 2)))

p⊨s1 : {p : Prog s0} → p ⊨ ◇ (at "s1")
p⊨s1 = enterBlock s0 (◇-i init)

s1=>s2 : {p : Prog s0} → p ⊨ ◇ (at "s1") → p ⊨ ◇ (at "s2")
s1=>s2 x = flow s0 (record {}) (:=n-step s1 x)

s2=>s4 : {p : Prog s0} → p ⊨ ◇ (at "s2") → p ⊨ ◇ (at "s4")
s2=>s4 x = flow s2 (record {}) (:=n-step s3 (enterBlock s2 x))

s4=>s4' : {p : Prog s0} → p ⊨ ◇ (at "s4") → p ⊨ ◇ (af "s4")
s4=>s4' x = exitPar s4 (join s4 (:=n-step s5 (◇-∧-e₁ (enterPar s4 x))) (:=n-step s6 (◇-∧-e₂ (enterPar s4 x))))

s4=>s2' : {p : Prog s0} → p ⊨ ◇ (at "s4") → p ⊨ ◇ (af "s2")
s4=>s2' x = exitBlock s2 (record {}) (s4=>s4' x)

s1=>s0' : {p : Prog s0} → p ⊨ ◇ (at "s1") → p ⊨ ◇ (af "s0")
s1=>s0' x = exitBlock s0 (record {}) (s4=>s2' (s2=>s4 (s1=>s2 (enterBlock s0 (◇-i init)))))

-- exitBlock s0 (record {}) (s2=>s2' (s1=>s2 x))
{-}
p' : {p : Prog s0} → p ⊨ term
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
