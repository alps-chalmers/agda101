module Rules where

open import Translator
open import LTL
open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Label

_==_ : ℕ → ℕ → Bool
zero == zero = true
zero == suc y = false
suc x == zero = false
suc x == suc y = x == y

data _⊢_ : LTL → LTL → Set where

-- Index with rule and ltl
data Rule : Set where
  assRule   : LTL → Rule
  parRule   : LTL → Rule
  seqRule   : LTL → Rule
  whileRule : LTL → Rule
  orRule    : LTL → Rule
  dummy     : LTL → Rule
  inInf     : LTL → Rule
  atomLive  : LTL → Rule
  customR   :  ℕ → LTL → Rule
  exitRule  : LTL → Rule
  □-e       : LTL → Rule
  ∧'-e1      : LTL → Rule
  ∧'-e2      : LTL → Rule
  ∧'-i       : LTL → Rule

-- Add action reference

data Ru : LTL → Set where
  id    : (φ : LTL) → Ru φ
  ∧'-i   : {φ ψ : LTL} → Ru φ → Ru ψ → Ru (φ ∧' ψ)
  ∧'-e₁  : {φ ψ : LTL} → Ru (φ ∧' ψ) → Ru φ
  inInf : {l : Label} → Ru (in' l) → Ru ((at l) ∨' (after l))

data Valid : Set where
  yes : {φ : LTL} → Ru φ → Valid
  no  : Valid -- TODO Add error' message

extract : {φ : LTL} → Ru φ → LTL
extract {φ} _ = φ

f : (φ : LTL) → Ru φ
f x = id x

r-∧'-i : {φ ψ : LTL} → Ru (φ) → Ru (ψ) → Valid
r-∧'-i r₁ r₂ = yes (∧'-i r₁ r₂)

r-∧'-e₁ : LTL → Valid
r-∧'-e₁ (φ ∧' ψ) = yes (∧'-e₁ (id (φ ∧' ψ)))
r-∧'-e₁ _ = no


test : Valid
test = r-∧'-e₁ (extract (id (at (s 0))))

{-test : (φ : LTL) → Ru (φ ∧' φ)
test x = r-∧'-i (id x) (id x)-}

r-inInf : LTL → Valid
r-inInf (in' l) = yes (inInf (id (in' l)))
r-inInf _ = no

extLTL : Rule → LTL
extLTL (assRule φ) = φ
extLTL (parRule φ) = φ
extLTL (seqRule φ) = φ
extLTL (whileRule φ) = φ
extLTL (orRule φ) = φ
extLTL (dummy φ) = φ
extLTL (inInf φ) = φ
extLTL (□-e φ) = φ
extLTL (∧'-e1 φ) = φ
extLTL (∧'-e2 φ) = φ
extLTL (customR _ φ) = φ
extLTL (atomLive φ) = φ
extLTL (exitRule φ) = φ
extLTL (∧'-i φ) = φ

isEq : (φ : LTL) → (ψ : LTL) → Bool
isEq T' T' = true
isEq ⊥ ⊥ = true
isEq (∼ x) (∼ y) = isEq x y
isEq (□ x) (□ y) = isEq x y
isEq (◇ x) (◇ y) = isEq x y
isEq (x₁ ∧' x₂) (y₁ ∧' y₂) = (isEq x₁ y₂) ∧ ((isEq x₁ y₂))
isEq (x₁ ∨' x₂) (y₁ ∨' y₂) = (isEq x₁ y₂) ∧ ((isEq x₁ y₂))
isEq (x₁ ⇒ x₂) (y₁ ⇒ y₂) = (isEq x₁ y₂) ∧ ((isEq x₁ y₂))
isEq (x₁ ~> x₂) (y₁ ~> y₂) = (isEq x₁ y₂) ∧ ((isEq x₁ y₂))
isEq (at (s x)) (at (s y)) = x == y
isEq (after (s x)) (after (s y)) = x == y
isEq (x₁ EQ x₂) (y₁ EQ y₂) = ((x₁ == y₁)) ∧ (x₂ == y₂)
isEq _ _ = false

isEqA : Action → Action → Bool
isEqA assign assign = true
isEqA par par = true
isEqA seq sewq = true
isEqA _ _ = false

legalApplication : List TransRel → Action → LTL → Maybe LTL
legalApplication [] a l = nothing
legalApplication (todo ∷ ts) a l = legalApplication ts a l
legalApplication (< pre > a' < post > ∷ ts) a l = if (isEq l pre) ∧ isEqA a a' then just post else legalApplication ts a l

extAction : Rule → Action
extAction (assRule _) = assign
extAction (parRule _) = par
extAction (seqRule _) = seq
extAction (whileRule _) = while
extAction (orRule _) = or'
extAction (dummy _) = dummy
extAction (inInf _) = inInf
extAction (□-e _) = □-e
extAction (∧'-e1 _) = ltl
extAction (∧'-e2 _) = ltl
extAction (atomLive _) = ltl
extAction (exitRule _ ) = ltl
extAction (customR n _) = custom n
extAction (∧'-i _) = ltl

applyRule : List TransRel → LTL → Rule → LTL
applyRule ts ls r with legalApplication ts (extAction r) (extLTL r)
... | just post = if isEq (extLTL r) ls then post else ⊥
... | nothing = ⊥

{-}
applyRule : List TransRel → LTL → Rule → LTL
applyRule ts ls (assRule φ) with legalApplication ts assign φ
... | just post = if isEq φ ls then post else ⊥
... | nothing = ⊥
applyRule ts ls (parRule φ) with legalApplication ts par φ
... | just post = if isEq φ ls then post else ⊥
... | nothing = ⊥
applyRule ts ls (seqRule φ) with legalApplication ts seq φ
... | just post = if isEq φ ls then post else ⊥
... | nothing = ⊥
-- applyRule ts ls (andRule1 (φ ∧' ψ)) = φ
-- applyRule ts ls (andRule2 (φ ∧' ψ)) = ψ
-- applyRule _ _ _ = ⊥
-}
