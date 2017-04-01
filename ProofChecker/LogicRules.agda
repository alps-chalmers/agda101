module LogicRules where

open import Props
open import Ctx
open import Data.Nat

data _⊢_ : {n : ℕ} → (Γ : Ctx n) → (ψ : Props) → Set where
  var   : ∀{n} {Γ : Ctx n} {ψ} → (Γ ⋆ ψ) ⊢ ψ
  weak  : ∀{n} {Γ : Ctx n} {φ ψ} → Γ ⊢ ψ → (Γ ⋆ φ) ⊢ ψ
  T-i   : ∀{n} {Γ : Ctx n} → Γ ⊢ T
  ⊥-e   : ∀{n} {Γ : Ctx n} {ψ} → Γ ⊢ ⊥ → Γ ⊢ ψ
  ~-i   : ∀{n} {Γ : Ctx n} {φ} → (Γ ⋆ φ) ⊢ ⊥ → Γ ⊢ (~ φ)
  ~-e   : ∀{n} {Γ : Ctx n} {φ} → Γ ⊢ φ → Γ ⊢ (~ φ) → Γ ⊢ ⊥
  ⇒-i   : ∀{n} {Γ : Ctx n} {φ ψ} → (Γ ⋆ φ) ⊢ ψ → Γ ⊢ (φ ⇒ ψ)
  ⇒-e   : ∀{n} {Γ : Ctx n} {φ ψ} → Γ ⊢ (φ ⇒ ψ) → Γ ⊢ φ → Γ ⊢ ψ
  ∧-i   : ∀{n} {Γ : Ctx n} {φ ψ} → Γ ⊢ φ → Γ ⊢ ψ → Γ ⊢ (φ ∧ ψ)
  ∧-e₁  : ∀{n} {Γ : Ctx n} {φ ψ} → Γ ⊢ (φ ∧ ψ) → Γ ⊢ φ
  ∧-e₂  : ∀{n} {Γ : Ctx n} {φ ψ} → Γ ⊢ (φ ∧ ψ) → Γ ⊢ ψ
  ∨-i₁  : ∀{n} {Γ : Ctx n} {φ ψ} → Γ ⊢ φ → Γ ⊢ (φ ∨ ψ)
  ∨-i₂  : ∀{n} {Γ : Ctx n} {φ ψ} → Γ ⊢ ψ → Γ ⊢ (φ ∨ ψ)
  ∨-e   : ∀{n} {Γ : Ctx n} {φ ψ χ} → Γ ⊢ (φ ∨ ψ) → (Γ ⋆ φ) ⊢ χ → (Γ ⋆ ψ) ⊢ χ → Γ ⊢ χ
  lem   : ∀{n} {Γ : Ctx n} {φ} → Γ ⊢ (φ ∨ (~ φ))


∧-comm : {φ ψ : Props} {n : ℕ} {Γ : Ctx n} → Γ ⊢ (φ ∧ ψ) → Γ ⊢ (ψ ∧ φ)
∧-comm p = ∧-i (∧-e₂ p) (∧-e₁ p)

∨-comm : {φ ψ : Props} {n : ℕ} {Γ : Ctx n} → Γ ⊢ (φ ∨ ψ) → Γ ⊢ (ψ ∨ φ)
∨-comm p = ∨-e p (∨-i₂ var) (∨-i₁ var)

∧→∨ : {φ ψ : Props} {n : ℕ} {Γ : Ctx n} → Γ ⊢ (φ ∧ ψ) → Γ ⊢ (φ ∨ ψ)
∧→∨ p = ∨-i₂ (∧-e₂ p)
