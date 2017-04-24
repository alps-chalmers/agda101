module Proof where

open import Label
open import Data.Nat
open import Data.String
open import Data.Bool as Bool using (Bool; true; false)
open import LTL
open import Program

data _⊨_ : {i : Label} → (pr : Prog i) → LTL → Set where

  -- Program Rules
  init      : ∀ {i} → (p : Prog i) → p ⊨ (at i)
  :=n-R     : ∀ {i} {l₁ l₂ : Label} {x : String} {n : ℕ*} {p : Prog i}  → p ⊨ (at l₁) → Seg l₁ (x :=n n) l₂ → p ⊨ (after l₁ ∧ ("x" ==n n))
  :=b-T-R   : ∀ {i} {l₁ l₂ : Label} {x : String} {p : Prog i}           → p ⊨ (at l₁) → Seg l₁ (x :=b (bool true)) l₂ → p ⊨ (after l₁ ∧ (tr (var x)))
  :=b-F-R   : ∀ {i} {l₁ l₂ : Label} {x : String} {p : Prog i}           → p ⊨ (at l₁) → Seg l₁ (x :=b (bool false)) l₂ → p ⊨ (after l₁ ∧ (∼ (tr (var x))))
  :=bVar-R  : ∀ {i} {l₁ l₂ : Label} {x y : String} {p : Prog i}         → p ⊨ (at l₁) → Seg l₁ (x :=b (var y)) l₂ → p ⊨ (after l₁ ∧ (x ==b (var y)))
  flow      : ∀ {i} {l₁ l₂ : Label} {e : Stm} {p : Prog i}              → p ⊨ (after l₁) → Seg l₁ e l₂ → p ⊨ (at l₂)
  parRule   : ∀ {i} {p : Prog i} {l l' a b : Label}                     → p ⊨ (at l) → Seg l (a || b) l' → p ⊨ ((at a) ∧ (at b))
  exitPar   : ∀ {i} {p : Prog i} {l l' a b : Label}                     → p ⊨ ((after a) ∧ (after b)) → Seg l (a || b) l' → p ⊨ (after l)
  exitWhile : ∀ {i} {p : Prog i} {l l' s : Label} {b : Bool*}           → p ⊨ ((at l) ∧ (□ (∼ (tr b)))) → Seg l (while b s) l' → p ⊨ (after l)
  exWhile-F : ∀ {i} {p : Prog i} {l l' s : Label}                       → p ⊨ (at l) → Seg l (while (bool false) s) l' → p ⊨ (after l)
  exWhile-E : ∀ {i} {p : Prog i} {l l' s : Label} {x y : ℕ}             → p ⊨ (at l) → Seg l (while ((nat x) <' (nat y)) s) l' → p ⊨ (after l)
  ifRule    : ∀ {i} {p : Prog i} {l l' s : Label} {b : Bool*}           → p ⊨ (at l) → Seg l (if b s) l' → p ⊨ ((at s) ∨ (after l))
  at=>af'   : ∀ {i} {p : Prog i} {l₁ : Label}                           → p ⊨ (at l₁) → p ⊨ (∼ (after l₁))

  -- LTL Rules
  ∧-e₁      : ∀ {i} {φ ψ : LTL} {p : Prog i}    → p ⊨ (φ ∧ ψ) → p ⊨ φ
  ∧-e₂      : ∀ {i} {φ ψ : LTL} {p : Prog i}    → p ⊨ (φ ∧ ψ) → p ⊨ ψ
  ∧-i       : ∀ {i} {φ ψ : LTL} {p : Prog i}    → p ⊨ φ → p ⊨ ψ → p ⊨ (φ ∧ ψ)
  ⇒-e       : ∀ {i} {φ ψ : LTL} {p : Prog i}    → p ⊨ (φ ⇒ ψ) → p ⊨ φ → p ⊨ ψ
  □-∧-e₁    : ∀ {i} {φ ψ : LTL} {p : Prog i}    → p ⊨ □(φ ∧ ψ) → p ⊨ □ φ
  □-∧-e₂    : ∀ {i} {φ ψ : LTL} {p : Prog i}    → p ⊨ □(φ ∧ ψ) → p ⊨ □ ψ
  T-i       : ∀ {i} {p : Prog i}                → p ⊨ T
  LEM       : ∀ {i} {p : Prog i} {φ : LTL}      → p ⊨ (φ ∨ (∼ φ))
  ∨-i₁      : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ φ → p ⊨ (φ ∨ ψ)
  ∨-i₂      : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ ψ → p ⊨ (φ ∨ ψ)
  ∨-e       : ∀ {i} {p : Prog i} {φ ψ χ : LTL}  → p ⊨ (φ ∨ ψ) → p ⊨ (φ ⇒ χ) → p ⊨ (ψ ⇒ χ) → p ⊨ χ
  ⇒-i       : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ ((∼ φ) ∨ ψ) → p ⊨ (φ ⇒ ψ)
  ⊥-e       : ∀ {i} {p : Prog i} {φ : LTL}      → p ⊨ ⊥ → p ⊨ φ
  in⇒at     : ∀ {i} {p : Prog i} {l : Label}    → p ⊨ (in' l) → p ⊨ (at l)
  □⇒~>      : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ (□(φ ⇒ ψ)) → p ⊨ (φ ~> ψ)
  □-∧-exp   : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ (□(φ ∧ ψ)) → p ⊨ ((□ φ) ∧ (□ ψ))
  □-∨-exp   : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ (□(φ ∨ ψ)) → p ⊨ ((□ φ) ∨ (□ ψ))
  ◇-∧-exp   : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ (◇(φ ∧ ψ)) → p ⊨ ((◇ φ) ∧ (◇ ψ))
  ◇-∨-exp   : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ (◇(φ ∨ ψ)) → p ⊨ ((◇ φ) ∨ (◇ ψ))
  TL5       : ∀ {i} {p : Prog i} {φ ψ : LTL}    → p ⊨ ((□ φ) ∧ (□ (φ ⇒ ψ))) → p ⊨ (□ ψ)
  TL6       : ∀ {i} {p : Prog i} {φ : LTL}      → p ⊨ ((◇ φ) ∨ (□ (∼ φ)))
  -- Custom axioms
  custom : ∀ {i} {p : Prog i} (φ : LTL) → (ψ : LTL) → p ⊨ (φ ⇒ ψ)



{-==============================
            THEOREMS
==============================-}

∧-comm : {l : Label} → {p : Prog l} → {φ ψ : LTL} → p ⊨ (φ ∧ ψ) → p ⊨ (ψ ∧ φ)
∧-comm p = ∧-i (∧-e₂ p) (∧-e₁ p)

∧⇒∨ : {l : Label} → {p : Prog l} {φ ψ : LTL} → p ⊨ (φ ∧ ψ) → p ⊨ (φ ∨ ψ)
∧⇒∨ p = ∨-i₁ (∧-e₁ p)
