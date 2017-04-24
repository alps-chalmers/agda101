module LTLRules where

open import Label
open import Data.Nat
open import Data.String
open import Data.Bool as Bool using (Bool; true; false)
open import LTL
open import Program

-- pr ⊨ φ, the program pr satiesfies φ when starting at the segment labled i.

data _⊨_ : {i : Label} {n : ℕ} → (pr : Prog i n) → (φ : LTL) → Set where

  -- Program Rules
  init      : ∀ {i n}                           → (p : Prog i n) → p ⊨ (at i)
  :=n-R     : ∀ {i n l l' x v} {p : Prog i n}   → p ⊨ (at l) → Seg l (x :=n v) l' → p ⊨ (after l ∧ ("x" ==n v))
  :=b-T-R   : ∀ {i n l l' x} {p : Prog i n}     → p ⊨ (at l) → Seg l (x :=b (bool true)) l' → p ⊨ (after l ∧ (tr (var x)))
  :=b-F-R   : ∀ {i n l l' x} {p : Prog i n}     → p ⊨ (at l) → Seg l (x :=b (bool false)) l' → p ⊨ (after l ∧ (∼ (tr (var x))))
  :=bVar-R  : ∀ {i n l l' x y} {p : Prog i n}   → p ⊨ (at l) → Seg l (x :=b (var y)) l' → p ⊨ (after l ∧ (x ==b (var y)))
  flow      : ∀ {i n l l' stm} {p : Prog i n}   → p ⊨ (after l) → Seg l stm l' → p ⊨ (at l')
  parRule   : ∀ {i n l l' a b} {p : Prog i n}   → p ⊨ (at l) → Seg l (a || b) l' → p ⊨ ((at a) ∧ (at b))
  exitPar   : ∀ {i n l l' a b} {p : Prog i n}   → p ⊨ ((after a) ∧ (after b)) → Seg l (a || b) l' → p ⊨ (after l)
  exitWhile : ∀ {i n l l' s b} {p : Prog i n}   → p ⊨ ((at l) ∧ (□ (∼ (tr b)))) → Seg l (while b s) l' → p ⊨ (after l)
  exWhile-F : ∀ {i n l l' s} {p : Prog i n}     → p ⊨ (at l) → Seg l (while (bool false) s) l' → p ⊨ (after l)
  exWhile-E : ∀ {i n l l' s x y} {p : Prog i n} → p ⊨ (at l) → Seg l (while ((nat x) <' (nat y)) s) l' → p ⊨ (after l)
  ifRule    : ∀ {i n l l' s b} {p : Prog i n}   → p ⊨ (at l) → Seg l (if b s) l' → p ⊨ ((at s) ∨ (after l))
  at=>af'   : ∀ {i n l} {p : Prog i n}          → p ⊨ (at l) → p ⊨ (∼ (after l))

  -- LTL Rules
  T-i       : ∀ {i n} {p : Prog i n}        → p ⊨ T
  var       : ∀ {i n φ} {p : Prog i n}      → (p ⋆ φ) ⊨ φ
  LEM       : ∀ {i n φ} {p : Prog i n}      → p ⊨ (φ ∨ (∼ φ))
  TL6       : ∀ {i n φ} {p : Prog i n}      → p ⊨ ((◇ φ) ∨ (□ (∼ φ)))
  ⊥-e       : ∀ {i n φ} {p : Prog i n}      → p ⊨ ⊥ → p ⊨ φ
  in⇒at     : ∀ {i n l} {p : Prog i n}      → p ⊨ (in' l) → p ⊨ (at l)
  ∧-e₁      : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ (φ ∧ ψ) → p ⊨ φ
  ∧-e₂      : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ (φ ∧ ψ) → p ⊨ ψ
  ∧-i       : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ φ → p ⊨ ψ → p ⊨ (φ ∧ ψ)
  ⇒-e       : ∀ {i n φ ψ} {p : Prog i n}    → (p ⋆ φ) ⊨ ψ → p ⊨ φ → p ⊨ ψ
  □-∧-e₁    : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ □(φ ∧ ψ) → p ⊨ □ φ
  □-∧-e₂    : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ □(φ ∧ ψ) → p ⊨ □ ψ
  ∨-i₁      : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ φ → p ⊨ (φ ∨ ψ)
  ∨-i₂      : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ ψ → p ⊨ (φ ∨ ψ)
  ⇒-i       : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ ((∼ φ) ∨ ψ) → p ⊨ (φ ⇒ ψ)
  □⇒~>      : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ (□(φ ⇒ ψ)) → p ⊨ (φ ~> ψ)
  □-∧-exp   : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ (□(φ ∧ ψ)) → p ⊨ ((□ φ) ∧ (□ ψ))
  □-∨-exp   : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ (□(φ ∨ ψ)) → p ⊨ ((□ φ) ∨ (□ ψ))
  ◇-∧-exp   : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ (◇(φ ∧ ψ)) → p ⊨ ((◇ φ) ∧ (◇ ψ))
  ◇-∨-exp   : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ (◇(φ ∨ ψ)) → p ⊨ ((◇ φ) ∨ (◇ ψ))
  ∨-e       : ∀ {i n φ ψ χ} {p : Prog i n}  → p ⊨ (φ ∨ ψ) → (p ⋆ φ) ⊨ χ → (p ⋆ ψ) ⊨ χ → p ⊨ χ
  TL5       : ∀ {i n φ ψ} {p : Prog i n}    → p ⊨ ((□ φ) ∧ (□ (φ ⇒ ψ))) → p ⊨ (□ ψ)
  -- Custom axioms
  custom    : ∀ {i n} {p : Prog i n} → (φ : LTL) → (ψ : LTL) → p ⊨ φ → p ⊨ ψ



{-==============================
            THEOREMS
==============================-}

∧-comm : ∀{l n φ ψ} {p : Prog l n} → p ⊨ (φ ∧ ψ) → p ⊨ (ψ ∧ φ)
∧-comm p = ∧-i (∧-e₂ p) (∧-e₁ p)

∨-comm : ∀{l n φ ψ} {p : Prog l n} → p ⊨ (φ ∨ ψ) → p ⊨ (ψ ∨ φ)
∨-comm p = ∨-e p (∨-i₂ var) (∨-i₁ var)

∧⇒∨ : ∀{l n} {p : Prog l n} {φ ψ : LTL} → p ⊨ (φ ∧ ψ) → p ⊨ (φ ∨ ψ)
∧⇒∨ p = ∨-i₁ (∧-e₁ p)
