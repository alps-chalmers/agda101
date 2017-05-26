module SatRel where

open import Data.Nat
open import Data.Bool as Bool using (Bool; true; false)
open import Data.String
open import ELTL
open import Program

-- TODO
-- * Fix loop conditions being able to handle infinite inner loops. in => at etc.
-- * Separate ELTLRules from the rest, into ⊢.
-- Make list of program, check if statement in the list

-- pr ⊨ φ, the Procram pr satiesfies φ when starting at the segment labled i.

data _⊨_ : {n : ℕ} {i l : Label} {pr : Proc i l} → (prg : Prog pr n) → (φ : ELTL) → Set where

  -- Procram Rules
  init       : ∀ {n p i} {ps : Proc p i} {pr : Prog ps n}               → pr ⊨ (at i)
  :=n-R      : ∀ {n p se l l' x v}    {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → Seg l (x :=n v) l' → pr ⊨ ◇ (after l ∧ (b* (x ==n v)))
  :=b-T-R    : ∀ {n p se l l' x}      {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → Seg l (x :=b (bool true)) l' → pr ⊨ ◇ (after l ∧ (b* (x ==b (bool true))))
  :=b-F-R    : ∀ {n p se l l' x}      {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → Seg l (x :=b (bool false)) l' → pr ⊨ ◇ (after l ∧ (b* (x ==b (bool false))))
  flow       : ∀ {n p se l l' stm}    {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (after l) → Seg l stm l' → pr ⊨ ◇ (at l')
  :=bVar-R   : ∀ {n p se l l' x y}    {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → Seg l (x :=b (var y)) l' → pr ⊨ ◇ (after l ∧ (b* (x ==b (var y))))
  exitSeg    : ∀ {n p se l}           {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → pr ⊨ (◇ (□ (in' l)) ∨ ◇ (after l))
  exitPar    : ∀ {n p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps n} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → pr ⊨ ◇ (after p₁) → pr ⊨  ◇ (after p₂) → Seg l (a || b) l' → pr ⊨ ◇ (after l)
  exitWhileT : ∀ {n p se l l' st b}   {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → pr ⊨ ◇ (□ (b* (b ==b (bool false)))) → Seg l (while (var b) st) l' → pr ⊨ ◇ (after l)


  exWhile-F  : ∀ {n p se l l' s}      {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → Seg l (while (bool false) s) l' → pr ⊨ ◇ (after l)
  fin-R      : ∀ {n p se l p' i}      {ps : Proc p se} {pr : Prog ps n} {ps' : Proc p' i} → pr ⊨ ◇ (at l) → Seg l (fin ps') l → pr ⊨ ◇ (after p')
  in=>at∨inw : ∀ {n p se l l' st b}   {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (in' l) → Seg l (while b st) l' → pr ⊨ ((◇ (at l)) ∨ (◇ (at st)))
  in=>at∨ini : ∀ {n p se l l' st b}   {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (in' l) → Seg l (if b st) l' → pr ⊨ ((◇ (at l)) ∨ (◇ (at st)))
  stuckWhile : ∀ {n p se l l' st}     {ps : Proc p se} {pr : Prog ps n} → Seg l (while (bool true) st) l' → pr ⊨ ((◇ (at l)) ⇒ (◇ (□ (in' l))))
  parRule    : ∀ {n p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps n} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → pr ⊨ ◇ (at l) → Seg l (a || b) l' → pr ⊨ ◇ ((at a₀) ∧ (at b₀))
  -- Program rules using ~>

  :=n-flow'  : ∀ {n p se l l' x v}  {ps : Proc p se} {pr : Prog ps n} → Seg l (x :=n v) l' → pr ⊨ (at l ~> after l)
  :=b-flow'   : ∀ {n p se l l' x b} {ps : Proc p se} {pr : Prog ps n} → Seg l (x :=b b) l' → pr ⊨ (at l ~> after l)
  :=n-R'     : ∀ {n p se l l' x v}  {ps : Proc p se} {pr : Prog ps n} → Seg l (x :=n v) l' → pr ⊨ (at l ~> (after l ∧ (b* (x ==n v))))
  :=b-T-R'   : ∀ {n p se l l' x}    {ps : Proc p se} {pr : Prog ps n} → Seg l (x :=b (bool true)) l' → pr ⊨ (at l ~> (after l ∧ (b* (x ==b (bool true)))))
  :=b-F-R'   : ∀ {n p se l l' x}    {ps : Proc p se} {pr : Prog ps n} → Seg l (x :=b (bool false)) l' → pr ⊨ (at l ~> (after l ∧ (b* (x ==b (bool false)))))
  flow'      : ∀ {n p se l l' stm}  {ps : Proc p se} {pr : Prog ps n} → Seg l stm l' → pr ⊨ ((after l) ~> (at l'))
  flowInv'    : ∀ {n p se l l' stm} {ps : Proc p se} {pr : Prog ps n} → Seg l stm l' → pr ⊨ ((at l') ~> (at l))
  exitWhile' : ∀ {n p se l l' st b}   {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (at l ~> □ (b* (b ==b (bool false)))) → pr ⊨ (in' l ~> at l) → Seg l (while (var b) st) l' → pr ⊨ (at l ~> after l)
  exitWhileF' : ∀ {n p se l l' st b}   {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (at l ~> □ (b* (b ==b (bool true)))) → pr ⊨ (in' l ~> at l) → Seg l (while (b ==b (bool false)) st) l' → pr ⊨ (at l ~> after l)
  exWhileC<  : ∀ {n p se l l' st x} {i : ℕ} {ps : Proc p se} {pr : Prog ps n} → Seg l (while ((var x) <* (nat i)) st) l' → pr ⊨ ((at l ∧ (b* ((var x) <* (nat i)))) ~> after l)
  atomswap   : ∀ {n p se x y v₁ v₂} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (((b* (x ==n v₁)) ∧ (b* (y ==n v₂))) ~> ((b* (x ==n v₂)) ∧ (b* (y ==n v₁))))
  enterWhile' : ∀ {n p se l l' st b}   {ps : Proc p se} {pr : Prog ps n} → Seg l (while b st) l' → pr ⊨ (in' l ~> at st)
  exWhile-F' : ∀ {n p se l l' s}      {ps : Proc p se} {pr : Prog ps n} → Seg l (while (bool false) s) l' → pr ⊨ (at l ~> after l)
  wContFlow'  : ∀ {n p se l l' st b}   {ps : Proc p se} {pr : Prog ps n} → Seg l (while b st) l' → pr ⊨ ((at l) ~> ((at st) ∨ (after l)))
  fin-R'     : ∀ {n p se l p' i}      {ps : Proc p se} {pr : Prog ps n} {ps' : Proc p' i} → Seg l (fin ps') l → pr ⊨ ((at l) ~> (after p'))
  exitPar'   : ∀ {n p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps n} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → Seg l (a || b) l' → pr ⊨ (((after p₁) ∧ (after p₂)) ~> (after l))
  parRule'   : ∀ {n p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps n} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → Seg l (a || b) l' → pr ⊨ ((at l) ~> ((at p₁) ∧ (at p₂)))
  enterPrc'   : ∀ {n p p' se sg} {ps : Proc p se} {pr : Prog ps n} → Proc p' sg → pr ⊨ (at p' ~> at sg)
  infPrc'     : ∀ {n p p' se sg} {ps : Proc p se} {pr : Prog ps n} → Proc p' sg → pr ⊨ (at sg ~> at p')
  infPar₁'    : ∀ {n p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps n} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → Seg l (a || b) l' → pr ⊨ (at p₂ ~> at p₁)
  infPar₂'    : ∀ {n p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps n} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → Seg l (a || b) l' → pr ⊨ (at p₁ ~> at p₂)
  join'      : ∀ {n p se p₁ p₂ l l' a₀ b₀} {ps : Proc p se} {pr : Prog ps n} {a : Proc p₁ a₀} {b : Proc p₂ b₀} → Seg l (a || b) l' → pr ⊨ (at p₁ ~> after p₁) → pr ⊨ (at p₂ ~> after p₂) → pr ⊨ ((at p₁ ∧ at p₂) ~> (after p₁ ∧ after p₂))

  -- ELTL Rules
  T-i       : ∀ {n p se}       {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ T
  assume    : ∀ {n p se φ}     {ps : Proc p se} {pr : Prog ps n}    → (pr ⋆ φ) ⊨ φ
  weak      : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ψ → (pr ⋆ φ) ⊨ ψ
  LEM       : ∀ {n p se φ}     {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (φ ∨ (∼ φ))
  TL6       : ∀ {n p se φ}     {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ((◇ φ) ∨ (□ (∼ φ)))
  ⊥-e       : ∀ {n p se φ}     {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ⊥ → pr ⊨ φ
  -- in⇒at     : ∀ {n p se l}     {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (in' l) → pr ⊨ (at l)
  ∧-e₁      : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (φ ∧ ψ) → pr ⊨ φ
  ∧-e₂      : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (φ ∧ ψ) → pr ⊨ ψ
  ∧-i       : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ φ → pr ⊨ ψ → pr ⊨ (φ ∧ ψ)
  ∨-i₁      : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ φ → pr ⊨ (φ ∨ ψ)
  ∨-i₂      : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ψ → pr ⊨ (φ ∨ ψ)
  ∨-e       : ∀ {n p se φ ψ χ} {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (φ ∨ ψ) → (pr ⋆ φ) ⊨ χ → (pr ⋆ ψ) ⊨ χ → pr ⊨ χ
  ⇒-i       : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → (pr ⋆ φ) ⊨ ψ → pr ⊨ (φ ⇒ ψ)
  ⇒-e       : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (φ ⇒ ψ) → pr ⊨ φ → pr ⊨ ψ
  ~>-□      : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (φ ~> ψ) → pr ⊨ □ ((◇ φ) ⇒ (◇ ψ))
  ~>-∧-e₁   : ∀ {n p se φ ψ χ} {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (φ ~> (ψ ∧ χ)) → pr ⊨ (φ ~> ψ)
  ~>-∧-e₂   : ∀ {n p se φ ψ χ} {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (φ ~> (ψ ∧ χ)) → pr ⊨ (φ ~> χ)
  □-e       : ∀ {n p se φ}     {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ □ φ → pr ⊨ φ
  □-~>      : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (□ ((◇ φ) ⇒ (◇ ψ))) → pr ⊨ (φ ~> ψ)
  □-∧-i     : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ □ φ → pr ⊨ □ ψ → pr ⊨ □ (φ ∧ ψ)
  □-∧-e₁    : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ □(φ ∧ ψ) → pr ⊨ □ φ
  □-∧-e₂    : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ □ (φ ∧ ψ) → pr ⊨ □ ψ
  □-∧-exp   : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (□ (φ ∧ ψ)) → pr ⊨ ((□ φ) ∧ (□ ψ))
  □-∨-exp   : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (□ (φ ∨ ψ)) → pr ⊨ ((□ φ) ∨ (□ ψ))
  □-∧-◇     : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ □ φ → pr ⊨ ◇ ψ → pr ⊨ ◇ (φ ∧ ψ)
  □-⇒-i     : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → (pr ⋆ φ) ⊨ ◇ ψ → pr ⊨ □ (φ ⇒ (◇ ψ))
  ◇-i       : ∀ {n p se φ}     {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ φ → pr ⊨ ◇ φ
  ◇-∧-exp   : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (◇ (φ ∧ ψ)) → pr ⊨ ((◇ φ) ∧ (◇ ψ))
  ◇-∧-e₁    : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ◇ (φ ∧ ψ) → pr ⊨ ◇ φ
  ◇-∧-e₂    : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ◇ (φ ∧ ψ) → pr ⊨ ◇ ψ
  ◇-□-∧-i   : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ◇ (□ φ) → pr ⊨ ◇ (□ ψ) → pr ⊨ ◇ (□ (φ ∧ ψ))
  ◇-∨-exp   : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ (◇ (φ ∨ ψ)) → pr ⊨ ((◇ φ) ∨ (◇ ψ))
  ◇-□-e     : ∀ {n p se φ}     {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ◇ (□ φ)→ pr ⊨ ◇ φ
  TL5       : ∀ {n p se φ ψ}   {ps : Proc p se} {pr : Prog ps n}    → pr ⊨ ((□ φ) ∧ (□ (φ ⇒ ψ))) → pr ⊨ (□ ψ)

{-==============================
            THEOREMS
==============================-}

∧-comm : ∀ {n p se φ ψ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (φ ∧ ψ) → pr ⊨ (ψ ∧ φ)
∧-comm p = ∧-i (∧-e₂ p) (∧-e₁ p)

∧-trans : ∀ {n p se φ ψ χ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (φ ∧ ψ) → pr ⊨ (ψ ∧ χ) → pr ⊨ (φ ∧ χ)
∧-trans p q = ∧-i (∧-e₁ p) (∧-e₂ q)

∧⇒∨ : ∀ {n p se φ ψ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (φ ∧ ψ) → pr ⊨ (φ ∨ ψ)
∧⇒∨ p = ∨-i₁ (∧-e₁ p)

∨-comm : ∀ {n p se φ ψ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (φ ∨ ψ) → pr ⊨ (ψ ∨ φ)
∨-comm p = ∨-e p (∨-i₂ assume) (∨-i₁ assume)

⇒-trans : ∀ {n p se φ ψ χ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (φ ⇒ ψ) → pr ⊨ (ψ ⇒ χ) → pr ⊨ (φ ⇒ χ)
⇒-trans p q = ⇒-i (⇒-e (weak q) (⇒-e (weak p) assume))

:=n-step : ∀ {p se n l l' x v} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → Seg l (x :=n v) l' → pr ⊨ ◇ (at l')
:=n-step p se = flow (◇-∧-e₁ (:=n-R p se)) se

:=b-T-step : ∀ {p se n l l' x} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → Seg l (x :=b (bool true)) l' → pr ⊨ ◇ (at l')
:=b-T-step p se = flow (◇-∧-e₁ (:=b-T-R p se)) se

:=b-F-step : ∀ {p se n l l' x} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ ◇ (at l) → Seg l (x :=b (bool false)) l' → pr ⊨ ◇ (at l')
:=b-F-step p se = flow (◇-∧-e₁ (:=b-F-R p se)) se

~>-trans : ∀ {n p se φ ψ χ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (φ ~> ψ) → pr ⊨ (ψ ~> χ) → pr ⊨ (φ ~> χ)
~>-trans p q = □-~> (□-⇒-i (⇒-e (□-e (~>-□ (weak q))) (⇒-e (□-e (weak (~>-□ p))) assume)))

~>-refl : ∀ {n p se φ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (φ ~> φ)
~>-refl = □-~> (□-⇒-i assume)

~>-e : ∀ {n p se φ ψ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ (φ ~> ψ) → pr ⊨ ◇ φ → pr ⊨ ◇ ψ
~>-e p q = ⇒-e (□-e (~>-□ p)) q

:=n-step' : ∀ {p se n l l' x v} {ps : Proc p se} {pr : Prog ps n} → Seg l (x :=n v) l' → pr ⊨ (at l ~> at l')
:=n-step' x = ~>-trans (:=n-flow' x) (flow' x)

:=b-step' : ∀ {p se n l l' x b} {ps : Proc p se} {pr : Prog ps n} → Seg l (x :=b b) l' → pr ⊨ (at l ~> at l')
:=b-step' x = ~>-trans (:=b-flow' x) (flow' x)

□-◇ : ∀ {n p se φ} {ps : Proc p se} {pr : Prog ps n} → pr ⊨ □ φ → pr ⊨ ◇ φ
□-◇ p = ◇-i (□-e p)


-- TODO
-- Implement THIS http://oxij.org/note/BrutalDepTypes/
-- Do this for safety
