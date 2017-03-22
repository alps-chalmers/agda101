module Rules where

open import Translator
open import LTL
open import LTLRules
open import Lists
open import Bool
open import Maybe
open import Nat
open import Label

data _⊢_ : LTL → LTL → Set where

data Rule : Set where
  assRule : LTL → Rule
  parRule : LTL → Rule
  seqRule : LTL → Rule
  andRule1 : LTL → Rule
  andRule2 : LTL → Rule
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
isEqA par par = true
isEqA seq sewq = true
isEqA _ _ = false

legalApplication : List TransRel → Action → LTL → Maybe LTL
legalApplication empty a l = Nothing
legalApplication (todo :: ts) a l = legalApplication ts a l
legalApplication ([ pre ] a' [ post ] :: ts) a l = if (isEq l pre) && isEqA a a' then Just post else legalApplication ts a l

-- Skicka med segment?
applyRule : List TransRel → List LTL → Rule → LTL
applyRule ts ls (assRule φ) with legalApplication ts assign φ
... | Just post = if elem φ ls isEq then post else ⊥
... | Nothing = ⊥
applyRule ts ls (parRule φ) with legalApplication ts par φ
... | Just post = if elem φ ls isEq then post else ⊥
... | Nothing = ⊥
applyRule ts ls (seqRule φ) with legalApplication ts seq φ
... | Just post = if elem φ ls isEq then post else ⊥
... | Nothing = ⊥
applyRule ts ls (andRule1 (φ ∧ ψ)) = φ
applyRule ts ls (andRule2 (φ ∧ ψ)) = ψ
applyRule _ _ _ = ⊥
