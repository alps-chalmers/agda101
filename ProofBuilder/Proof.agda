module Proof where

open import Label
open import Data.Nat
open import Data.String
open import Data.Bool as Bool using (Bool; true; false)
open import LTL
open import Program

data Proof : LTL → Set where
  -- Program rules --
  assiRule  : {l₁ l₂ : Label} {x : String} {n : ℕ} → Proof (at l₁) → Stm l₁ (x := n) l₂ → Proof (after l₁ ∧ ("x" ==n n))
  flow      : {l₁ l₂ : Label} {e : Exp} → Proof (after l₁) → Stm l₁ e l₂ → Proof (at l₂)
  parRule   : {l l' a b : Label} → Proof (at l) → Stm l (a || b) l' → Proof ((at a) ∧ (at b))
  exitPar   : {l l' a b : Label} → Proof ((after a) ∧ (after b)) → Stm l (a || b) l' → Proof (after l)
  ifRule    : {l l' s : Label} {b : Bool} → Proof (at l) → Stm l (if b s) l' → Proof ((at s) ∨ (after l))
  exWhile-F : {l l' s : Label} → Proof (at l) → Stm l (while false s) l' → Proof (after l)
  at=>af'   : {l₁ : Label} → Proof (at l₁) → Proof (∼ (after l₁))
  -- LTL --
  T-i       :                 Proof T
  LEM       : {φ : LTL}     → Proof (φ ∨ (∼ φ))
  ∼-i       : {φ : LTL}     → Proof (φ ⇒ ⊥) → Proof (∼ φ)
  ∼-e       : {φ : LTL}     → Proof φ → Proof (∼ φ) → Proof ⊥
  ∧-i       : {φ ψ : LTL}   → Proof φ → Proof ψ → Proof (φ ∧ ψ)
  --        : {φ ψ : LTL}   → Proof φ ψ → Proof φ → Proof ψ
  ∧-e₁      : {φ ψ : LTL}   → Proof (φ ∧ ψ) → Proof φ
  ∧-e₂      : {φ ψ : LTL}   → Proof (φ ∧ ψ) → Proof ψ
  ∨-i₁      : {φ ψ : LTL}   → Proof φ → Proof (φ ∨ ψ)
  ∨-i₂      : {φ ψ : LTL}   → Proof ψ → Proof (φ ∨ ψ)
  ∨-e       : {φ ψ χ : LTL} → Proof (φ ∨ ψ) → Proof (φ ⇒ χ) → Proof (ψ ⇒ χ) → Proof χ
  ⇒-i       : {φ ψ : LTL}   → Proof ((∼ φ) ∨ ψ) → Proof (φ ⇒ ψ)
  ⊥-e       : {φ : LTL}     → Proof ⊥ → Proof φ
  in⇒at     : {l : Label}   → Proof (in' l) → Proof (at l)
  □⇒~>      : {φ ψ : LTL}   → Proof (□(φ ⇒ ψ)) → Proof (φ ~> ψ)
  □-∧-exp   : {φ ψ : LTL}   → Proof (□(φ ∧ ψ)) → Proof ((□ φ) ∧ (□ ψ))
  □-∨-exp   : {φ ψ : LTL}   → Proof (□(φ ∨ ψ)) → Proof ((□ φ) ∨ (□ ψ))
  ◇-∧-exp   : {φ ψ : LTL}   → Proof (◇(φ ∧ ψ)) → Proof ((◇ φ) ∧ (◇ ψ))
  ◇-∨-exp   : {φ ψ : LTL}   → Proof (◇(φ ∨ ψ)) → Proof ((◇ φ) ∨ (◇ ψ))
  TL5       : {φ ψ : LTL}   → Proof ((□ φ) ∧ (□ (φ ⇒ ψ))) → Proof (□ ψ)
  TL6       : {φ : LTL}     → Proof ((◇ φ) ∨ (□ (∼ φ)))

{-==============================
            THEOREMS
==============================-}

∧-comm : {φ ψ : LTL} → Proof (φ ∧ ψ) → Proof (ψ ∧ φ)
∧-comm p = ∧-i (∧-e₂ p) (∧-e₁ p)

∧⇒∨ : {φ ψ : LTL} → Proof (φ ∧ ψ) → Proof (φ ∨ ψ)
∧⇒∨ p = ∨-i₁ (∧-e₁ p)
