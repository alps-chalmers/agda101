module Rules where

open import Translator
open import LTL
open import Lists
open import Bool
open import Maybe
open import Nat
open import Label

data _⊢_ : LTL → LTL → Set where

data Rule : Set where
  assRule : LTL → Rule
-- axiom : {φ ψ : LTL} → φ ⊢ ψ → Rule
--  rel   : TransRel → Rule


isEq : (φ : LTL) → (ψ : LTL) → Bool
isEq T T = true
isEq ⊥ ⊥ = true
isEq (∼ x) (∼ y) = isEq x y
isEq (□ x) (□ y) = isEq x y
isEq (◇ x) (◇ y) = isEq x y
isEq (x₁ ∧ x₂) (y₁ ∧ y₂) = (isEq x₁ y₂) && ((isEq x₁ y₂))
isEq (x₁ ∨ x₂) (y₁ ∨ y₂) = (isEq x₁ y₂) && ((isEq x₁ y₂))
isEq (x₁ ⇒ x₂) (y₁ ⇒ y₂) = (isEq x₁ y₂) && ((isEq x₁ y₂))
isEq (x₁ ~> x₂) (y₁ ~> y₂) = (isEq x₁ y₂) && ((isEq x₁ y₂))
isEq (at (s x)) (at (s y)) = x == y
isEq (after (s x)) (after (s y)) = x == y
isEq (x₁ EQ x₂) (y₁ EQ y₂) = ((x₁ == y₁)) && (x₂ == y₂)
isEq _ _ = false

isEqA : Action → Action → Bool
isEqA assign assign = true

legalApplication : List TransRel → Action → LTL → Maybe LTL
legalApplication empty a l = Nothing
legalApplication (xD :: ts) a l = legalApplication ts a l
legalApplication ([ pre ] a' [ post ] :: ts) a l = if (isEq l pre) && isEqA a a' then Just post else legalApplication ts a l

-- Skicka med segment?
applyRule : List TransRel → List LTL → LTL → Rule → LTL
applyRule ts ls l (assRule φ) with legalApplication ts assign φ
... | Just post = if elem φ ls isEq then post else ⊥
... | Nothing = ⊥

-- applyRule ltls l (axiom {φ} {ψ} x) = ψ -- if φ in ltls then ψ else Fail
