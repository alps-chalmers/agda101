module LTLRules where

open import Label
open import Data.Nat
open import Data.String
open import Data.Bool as Bool using (Bool; true; false)
open import LTL
open import Program

-- pr ⊨ φ, the Procram pr satiesfies φ when starting at the segment labled i.

data _⊨_ : {i l : Label} {pr : Proc i l} → (prg : Prog pr) → (φ : LTL) → Set where

  -- Procram Rules
  init      : ∀ {p i} {ps : Proc p i} {pr : Prog ps}                → pr ⊨ (at i)
  :=n-R     : ∀ {p se l l' x v} {ps : Proc p se} {pr : Prog ps}     → pr ⊨ ◇ (at l) → Seg l (x :=n v) l' → pr ⊨ ◇ (after l ∧ ("x" ==n v))
  :=b-T-R   : ∀ {p se l l' x} {ps : Proc p se} {pr : Prog ps}       → pr ⊨ ◇ (at l) → Seg l (x :=b (bool true)) l' → pr ⊨ ◇ (after l ∧ (tr (var x)))
  :=b-F-R   : ∀ {p se l l' x} {ps : Proc p se} {pr : Prog ps}       → pr ⊨ ◇ (at l) → Seg l (x :=b (bool false)) l' → pr ⊨ ◇ (after l ∧ (∼ (tr (var x))))
  :=bVar-R  : ∀ {p se l l' x y} {ps : Proc p se} {pr : Prog ps}     → pr ⊨ ◇ (at l) → Seg l (x :=b (var y)) l' → pr ⊨ ◇ (after l ∧ (x ==b (var y)))
  flow      : ∀ {p se l l' stm} {ps : Proc p se} {pr : Prog ps}     → pr ⊨ ◇ (after l) → Seg l stm l' → pr ⊨ ◇ (at l')
  exitWhile : ∀ {p se l l' st b} {ps : Proc p se} {pr : Prog ps}    → pr ⊨ ◇ ((at l) ∧ (□ (∼ (tr b)))) → Seg l (while b st) l' → pr ⊨ ◇ (after l)
  exWhile-F : ∀ {p se l l' s} {ps : Proc p se} {pr : Prog ps}       → pr ⊨ ◇ (at l) → Seg l (while (bool false) s) l' → pr ⊨ ◇ (after l)
  exWhile-E : ∀ {p se l l' st x y} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ ◇ (at l) → Seg l (while ((nat x) <' (nat y)) st) l' → pr ⊨ ◇ (after l)
  ifRule    : ∀ {p se l l' st b} {ps : Proc p se} {pr : Prog ps}    → pr ⊨ ◇ (at l) → Seg l (if b st) l' → pr ⊨ ◇ ((at st) ∨ (after l))
  at=>af'   : ∀ {p se l} {ps : Proc p se} {pr : Prog ps}            → pr ⊨ ◇ (at l) → pr ⊨ ◇ (∼ (after l))
  fin-R     : ∀ {p se l p' i} {ps : Proc p se} {pr : Prog ps} {ps' : Proc p' i} → pr ⊨ ◇ (at l) → Seg l (fin ps') l → pr ⊨ ◇ (after p')
  exitPar   : ∀ {p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → pr ⊨ ◇ (after p₁) → pr ⊨  ◇ (after p₂) → Seg l (a || b) l' → pr ⊨ ◇ (after l)
  parRule   : ∀ {p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → pr ⊨ ◇ (at l) → Seg l (a || b) l' → pr ⊨ ◇ ((at a₀) ∧ (at b₀))

  -- LTL Rules
  T-i       : ∀ {p se} {ps : Proc p se} {pr : Prog ps}      → pr ⊨ T
  -- var       : ∀ {ps φ}   {pr : Prog ps}    → (pr ⋆ φ) ⊨ φ
  LEM       : ∀ {p se φ} {ps : Proc p se} {pr : Prog ps}    → pr ⊨ (φ ∨ (∼ φ))
  TL6       : ∀ {p se φ} {ps : Proc p se} {pr : Prog ps}    → pr ⊨ ((◇ φ) ∨ (□ (∼ φ)))
  ⊥-e       : ∀ {p se φ} {ps : Proc p se} {pr : Prog ps}    → pr ⊨ ⊥ → pr ⊨ φ
  in⇒at     : ∀ {p se l} {ps : Proc p se} {pr : Prog ps}    → pr ⊨ (in' l) → pr ⊨ (at l)
  ∧-e₁      : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ (φ ∧ ψ) → pr ⊨ φ
  ∧-e₂      : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ (φ ∧ ψ) → pr ⊨ ψ
  ∧-i       : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ φ → pr ⊨ ψ → pr ⊨ (φ ∧ ψ)
  -- ⇒-e       : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}    → (pr ⋆ φ) ⊨ ψ → pr ⊨ φ → pr ⊨ ψ
  ∨-i₁      : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ φ → pr ⊨ (φ ∨ ψ)
  ∨-i₂      : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ ψ → pr ⊨ (φ ∨ ψ)
  ⇒-i       : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ ((∼ φ) ∨ ψ) → pr ⊨ (φ ⇒ ψ)
  □⇒~>      : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ (□(φ ⇒ ψ)) → pr ⊨ (φ ~> ψ)
  □-∧-e₁    : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ □(φ ∧ ψ) → pr ⊨ □ φ
  □-∧-e₂    : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ □(φ ∧ ψ) → pr ⊨ □ ψ
  □-∧-exp   : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ (□(φ ∧ ψ)) → pr ⊨ ((□ φ) ∧ (□ ψ))
  □-∨-exp   : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ (□(φ ∨ ψ)) → pr ⊨ ((□ φ) ∨ (□ ψ))
  □-◇       : ∀ {p se φ} {ps : Proc p se} {pr : Prog ps}    → pr ⊨ □ φ → pr ⊨ ◇ φ
  ◇-i       : ∀ {p se φ} {ps : Proc p se} {pr : Prog ps}    → pr ⊨ φ → pr ⊨ ◇ φ
  ◇-∧-exp   : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ (◇(φ ∧ ψ)) → pr ⊨ ((◇ φ) ∧ (◇ ψ))
  ◇-∧-e₁    : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ ◇ (φ ∧ ψ) → pr ⊨ ◇ φ
  ◇-∧-e₂    : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ ◇ (φ ∧ ψ) → pr ⊨ ◇ ψ
  ◇-□-∧-i   : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ ◇ (□ φ) → pr ⊨ ◇ (□ ψ) → pr ⊨ ◇ (□ (φ ∧ ψ))
  ◇-∨-exp   : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ (◇(φ ∨ ψ)) → pr ⊨ ((◇ φ) ∨ (◇ ψ))
  -- ∨-e       : ∀ {ps φ ψ χ} {pr : Prog ps}  → pr ⊨ (φ ∨ ψ) → (pr ⋆ φ) ⊨ χ → (pr ⋆ ψ) ⊨ χ → pr ⊨ χ
  TL5       : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps}  → pr ⊨ ((□ φ) ∧ (□ (φ ⇒ ψ))) → pr ⊨ (□ ψ)
  -- Custom axioms
  custom    : ∀ {p se} {ps : Proc p se} {pr : Prog ps} → (φ : LTL) → (ψ : LTL) → pr ⊨ φ → pr ⊨ ψ

{-==============================
            THEOREMS
==============================-}


∧-comm : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps} → pr ⊨ (φ ∧ ψ) → pr ⊨ (ψ ∧ φ)
∧-comm p = ∧-i (∧-e₂ p) (∧-e₁ p)

-- ∨-comm : ∀{i l n φ ψ} {pr : Proc i l} → pr ⊨ (φ ∨ ψ) → pr ⊨ (ψ ∨ φ)
-- ∨-comm p = ∨-e p (∨-i₂ var) (∨-i₁ var)

∧⇒∨ : ∀ {p se φ ψ} {ps : Proc p se} {pr : Prog ps} → pr ⊨ (φ ∧ ψ) → pr ⊨ (φ ∨ ψ)
∧⇒∨ p = ∨-i₁ (∧-e₁ p)
