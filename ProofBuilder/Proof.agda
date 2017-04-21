module Proof where

open import Label
open import Data.Nat
open import Data.String
open import Data.Bool as Bool using (Bool; true; false)
open import LTL
open import Program

data Proof : LTL → Set where

  -- Program rules --
  :=n-R     : {l₁ l₂ : Label} {x : String} {n : ℕ*} → Proof (at l₁) → Seg l₁ (x :=n n) l₂ → Proof (after l₁ ∧ ("x" ==n n))
  :=b-T-R   : {l₁ l₂ : Label} {x : String} → Proof (at l₁) → Seg l₁ (x :=b (bool true)) l₂ → Proof (after l₁ ∧ (tr (var x)))
  :=b-F-R   : {l₁ l₂ : Label} {x : String} → Proof (at l₁) → Seg l₁ (x :=b (bool false)) l₂ → Proof (after l₁ ∧ (∼ (tr (var x))))
  :=bVar-R  : {l₁ l₂ : Label} {x y : String} → Proof (at l₁) → Seg l₁ (x :=b (var y)) l₂ → Proof (after l₁ ∧ (x ==b (var y)))
  flow      : {l₁ l₂ : Label} {e : Stm} → Proof (after l₁) → Seg l₁ e l₂ → Proof (at l₂)
  parRule   : {l l' a b : Label} → Proof (at l) → Seg l (a || b) l' → Proof ((at a) ∧ (at b))
  exitPar   : {l l' a b : Label} → Proof ((after a) ∧ (after b)) → Seg l (a || b) l' → Proof (after l)
  ifRule    : {l l' s : Label} {b : Bool*} → Proof (at l) → Seg l (if b s) l' → Proof ((at s) ∨ (after l))
  exWhile-F : {l l' s : Label} → Proof (at l) → Seg l (while (bool false) s) l' → Proof (after l)
  exWhile-E : {l l' s : Label} {x y : ℕ} → Proof (at l) → Seg l (while ((nat x) <' (nat y)) s) l' → Proof (after l)
  exitWhile : {l l' s : Label} {b : Bool*} → Proof ((at l) ∧ (□ (∼ (tr b)))) → Seg l (while b s) l' → Proof (after l)
  at=>af'   : {l₁ : Label} → Proof (at l₁) → Proof (∼ (after l₁))
  -- LTL --
  T-i       :                 Proof T
  LEM       : {φ : LTL}     → Proof (φ ∨ (∼ φ))
  ∼-i       : {φ : LTL}     → Proof (φ ⇒ ⊥) → Proof (∼ φ)
  ∼-e       : {φ : LTL}     → Proof φ → Proof (∼ φ) → Proof ⊥
  ∧-i       : {φ ψ : LTL}   → Proof φ → Proof ψ → Proof (φ ∧ ψ)
  ∧-e₁      : {φ ψ : LTL}   → Proof (φ ∧ ψ) → Proof φ
  ∧-e₂      : {φ ψ : LTL}   → Proof (φ ∧ ψ) → Proof ψ
  ∨-i₁      : {φ ψ : LTL}   → Proof φ → Proof (φ ∨ ψ)
  ∨-i₂      : {φ ψ : LTL}   → Proof ψ → Proof (φ ∨ ψ)
  ∨-e       : {φ ψ χ : LTL} → Proof (φ ∨ ψ) → Proof (φ ⇒ χ) → Proof (ψ ⇒ χ) → Proof χ
  ⇒-i       : {φ ψ : LTL}   → Proof ((∼ φ) ∨ ψ) → Proof (φ ⇒ ψ)
  ⇒-e       : {φ ψ : LTL}   → Proof (φ ⇒ ψ) → Proof φ → Proof ψ
  ⊥-e       : {φ : LTL}     → Proof ⊥ → Proof φ
  in⇒at     : {l : Label}   → Proof (in' l) → Proof (at l)
  □⇒~>      : {φ ψ : LTL}   → Proof (□(φ ⇒ ψ)) → Proof (φ ~> ψ)
  □-∧-e₁    : {φ ψ : LTL}   → Proof (□(φ ∧ ψ)) → Proof (□ φ)
  □-∧-e₂    : {φ ψ : LTL}   → Proof (□(φ ∧ ψ)) → Proof (□ ψ)
  □-∧-exp   : {φ ψ : LTL}   → Proof (□(φ ∧ ψ)) → Proof ((□ φ) ∧ (□ ψ))
  □-∨-exp   : {φ ψ : LTL}   → Proof (□(φ ∨ ψ)) → Proof ((□ φ) ∨ (□ ψ))
  ◇-∧-exp   : {φ ψ : LTL}   → Proof (◇(φ ∧ ψ)) → Proof ((◇ φ) ∧ (◇ ψ))
  ◇-∨-exp   : {φ ψ : LTL}   → Proof (◇(φ ∨ ψ)) → Proof ((◇ φ) ∨ (◇ ψ))
  TL5       : {φ ψ : LTL}   → Proof ((□ φ) ∧ (□ (φ ⇒ ψ))) → Proof (□ ψ)
  TL6       : {φ : LTL}     → Proof ((◇ φ) ∨ (□ (∼ φ)))
  -- custom axioms
  custom    : (φ : LTL) → (ψ : LTL) → Proof (φ ⇒ ψ)



{-==============================
            THEOREMS
==============================-}

∧-comm : {φ ψ : LTL} → Proof (φ ∧ ψ) → Proof (ψ ∧ φ)
∧-comm p = ∧-i (∧-e₂ p) (∧-e₁ p)

∧⇒∨ : {φ ψ : LTL} → Proof (φ ∧ ψ) → Proof (φ ∨ ψ)
∧⇒∨ p = ∨-i₁ (∧-e₁ p)
