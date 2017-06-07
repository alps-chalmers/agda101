module SatRel where

open import Data.Nat
open import Data.Bool as Bool using (Bool; true; false)
open import Data.String
open import ELTL
open import CPL

infixl 12 _⊨_


-- TODO
-- http://oxij.org/note/BrutalDepTypes/

-- p ⊨ φ, the Procram p satiesfies φ with the initial statement st.

data _⊨_ {l : String} {s : Stm} {st : Stm* l s} : {n : ℕ} → (p : Prog st n) → ELTL → Set where

  -- Program rules

  init       : ∀ {n} {p : Prog st n}            → p ⊨ (at l)

  term       : ∀ {n} {p : Prog st n}            → p ⊨ (at l ~> af l)
                                                ---------------------
                                                → p ⊨ term

  :=n-R      : ∀ {n l x v} {p : Prog st n}      → Stm* l (x :=n v)
                                                --------------------------------------
                                                → p ⊨ (at l ~> (af l ∧ (b* (x ==n v))))

  :=b-T-R    : ∀ {n l x} {p : Prog st n}        → Stm* l (x :=b (bool true))
                                                --------------------------------------
                                                → p ⊨ (at l ~> (af l ∧ (b* (var x))))

  :=b-F-R    : ∀ {n l x} {p : Prog st n}        → Stm* l (x :=b (bool false))
                                                ------------------------------------------
                                                → p ⊨ (at l ~> (af l ∧ (b* (~ (var x)))))

  :=b-vT-R   : ∀ {n l x y} {p : Prog st n}      → Stm* l (x :=b (var y))
                                                -------------------------------------------------------
                                                → p ⊨ ((at l ∧ (b* (var y))) ~> (af l ∧ (b* (var x))))

  :=b-vF-R   : ∀ {n l x y} {p : Prog st n}      → Stm* l (x :=b (var y))
                                                ---------------------------------------------------------------
                                                → p ⊨ ((at l ∧ (b* (~ (var y)))) ~> (af l ∧ (b* ( ~(var x)))))

  flow       : ∀ {x y b bl n} {p : Prog st n}   → Stm* b (block bl)
                                                → x seq y ∈ bl
                                                ---------------------
                                                → p ⊨ (af x ~> at y)

  retWhile   : ∀ { l b bl n} {p : Prog st n}    → Stm* l (while b bl)
                                                ----------------------
                                                → p ⊨ (af bl ~> at l)

  exitWhileT : ∀ {l b n stm} {p : Prog st n}    → (s* : Stm* l (while (var b) stm))
                                                → p ⊨ (at l ~> □ (b* (~ (var b))))
                                                → p ⊨ (at stm ~> at l)
                                                ------------------------------------
                                                → p ⊨ (at l ~> af l)

  exitWhileF : ∀ {l b n stm} {p : Prog st n}    → (s* : Stm* l (while (~ (var b)) stm))
                                                → p ⊨ (at l ~> □ (b*  (var b)))
                                                → p ⊨ (at stm ~> at l)
                                                ----------------------------------------
                                                → p ⊨ (at l ~> af l)

  skipWhile  : ∀ {l n stm} {p : Prog st n}      → (s* : Stm* l (while (bool false) stm))
                                                -----------------------------------------
                                                → p ⊨ (at l ~> af l)

  enterBlock : ∀ {b bl n} {p : Prog st n}       → (s* : Stm* b (block bl))
                                                → (f : String)
                                                → f head bl
                                                ---------------------------
                                                → p ⊨ (at b ~> at f)

  exitBlock  : ∀ {bl b n f} {p : Prog st n}     → (s* : Stm* b (block bl))
                                                → fin bl f
                                                ---------------------------
                                                → p ⊨ (af f ~> af b)

  infBlock   : ∀ {bl b n} {p : Prog st n}       → (s* : Stm* b (block bl))
                                                → (stm : String)
                                                → stm ∈* bl
                                                ---------------------------
                                                → p ⊨ (at stm ~> at b)

  enterPar   : ∀ {l s₁ s₂ n} {p : Prog st n}    → (s* : Stm* l (s₁ || s₂))
                                                --------------------------------
                                                → p ⊨ (at l ~> (at s₁ ∧ at s₂))

  exitPar    : ∀ {l s₁ s₂ n} {p : Prog st n}    → (s* : Stm* l (s₁ || s₂))
                                                --------------------------------
                                                → p ⊨ ((af s₁ ∧ af s₂) ~> af l)

  infPar₁    : ∀ {l s₁ s₂ n} {p : Prog st n}    → (s* : Stm* l (s₁ || s₂))
                                                ---------------------------
                                                → p ⊨ (at s₂ ~> at s₁)

  infPar₂    : ∀ {l s₁ s₂ n} {p : Prog st n}    → (s* : Stm* l (s₁ || s₂))
                                                ---------------------------
                                                → p ⊨ (at s₁ ~> at s₂)

  join       : ∀ {l s₁ s₂ n} {p : Prog st n}    → (s* : Stm* l (s₁ || s₂))
                                                → p ⊨ (at s₁ ~> af s₁)
                                                → p ⊨ (at s₂ ~> af s₂)
                                                -------------------------------------------
                                                → p ⊨ ((at s₁ ∧ at s₂) ~> (af s₁ ∧ af s₂))

  -- LTL Rules

  T-i       : ∀ {n}         {p : Prog st n}     → p ⊨ T

  assume    : ∀ {n φ}       {p : Prog st n}     → (p ⋆ φ) ⊨ φ

  weak      : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ ψ
                                                --------------
                                                → (p ⋆ φ) ⊨ ψ

  LEM       : ∀ {n φ}       {p : Prog st n}     → p ⊨ (φ ∨ (∼ φ))

  TL6       : ∀ {n φ}       {p : Prog st n}     → p ⊨ ((◇ φ) ∨ (□ (∼ φ)))

  ⊥-e       : ∀ {n φ}       {p : Prog st n}     → p ⊨ ⊥
                                                --------
                                                → p ⊨ φ

  ∧-e₁      : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ (φ ∧ ψ)
                                                --------------
                                                → p ⊨ φ

  ∧-e₂      : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ (φ ∧ ψ)
                                                --------------
                                                → p ⊨ ψ

  ∧-i       : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ φ
                                                → p ⊨ ψ
                                                --------------
                                                → p ⊨ (φ ∧ ψ)

  ∨-i₁      : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ φ
                                                --------------
                                                → p ⊨ (φ ∨ ψ)

  ∨-i₂      : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ ψ
                                                --------------
                                                → p ⊨ (φ ∨ ψ)

  ∨-e       : ∀ {n φ ψ χ}   {p : Prog st n}     → p ⊨ (φ ∨ ψ)
                                                → (p ⋆ φ) ⊨ χ
                                                → (p ⋆ ψ) ⊨ χ
                                                --------------
                                                → p ⊨ χ

  ⇒-i       : ∀ {n φ ψ}     {p : Prog st n}     → (p ⋆ φ) ⊨ ψ
                                                --------------
                                                → p ⊨ (φ ⇒ ψ)

  ⇒-e       : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ (φ ⇒ ψ)
                                                ----------------
                                                → p ⊨ φ → p ⊨ ψ

  ~>-□      : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ (φ ~> ψ)
                                                ------------------------
                                                → p ⊨ □ ((◇ φ) ⇒ (◇ ψ))

  ~>-∧-e₁   : ∀ {n φ ψ χ}   {p : Prog st n}     → p ⊨ (φ ~> (ψ ∧ χ))
                                                ---------------------
                                                → p ⊨ (φ ~> ψ)

  ~>-∧-e₂   : ∀ {n φ ψ χ}   {p : Prog st n}     → p ⊨ (φ ~> (ψ ∧ χ))
                                                ---------------------
                                                → p ⊨ (φ ~> χ)

  □-e       : ∀ {n φ}       {p : Prog st n}     → p ⊨ □ φ
                                                ----------
                                                → p ⊨ φ

  □-mod     : ∀ {n φ ψ}     {p : Prog st n}     → (p ⋆ φ) ⊨ ψ
                                                --------------------
                                                → p ⊨ □ φ → p ⊨ □ ψ

  □-~>      : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ (□ ((◇ φ) ⇒ (◇ ψ)))
                                                --------------------------
                                                → p ⊨ (φ ~> ψ)

  □-∧-i     : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ □ φ
                                                → p ⊨ □ ψ
                                                ----------------
                                                → p ⊨ □ (φ ∧ ψ)

  □-∧-◇     : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ □ φ
                                                → p ⊨ ◇ ψ
                                                ----------------
                                                → p ⊨ ◇ (φ ∧ ψ)

  □-⇒-i     : ∀ {n φ ψ}     {p : Prog st n}     → (p ⋆ φ) ⊨ ◇ ψ
                                                --------------------
                                                → p ⊨ □ (φ ⇒ (◇ ψ))

  ◇-i       : ∀ {n φ}       {p : Prog st n}     → p ⊨ φ
                                                ----------
                                                → p ⊨ ◇ φ

  ◇-mod     : ∀ {n φ ψ}     {p : Prog st n}     → (p ⋆ φ) ⊨ ψ
                                                → p ⊨ ◇ φ
                                                --------------
                                                → p ⊨ ◇ ψ

  ◇-□-∧-i   : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ ◇ (□ φ)
                                                → p ⊨ ◇ (□ ψ)
                                                --------------------
                                                → p ⊨ ◇ (□ (φ ∧ ψ))

  ◇-∨-exp   : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ (◇ (φ ∨ ψ))
                                                ----------------------
                                                → p ⊨ ((◇ φ) ∨ (◇ ψ))

  ◇-□-e     : ∀ {n φ}       {p : Prog st n}     → p ⊨ ◇ (□ φ)
                                                --------------
                                                → p ⊨ ◇ φ

  TL5       : ∀ {n φ ψ}     {p : Prog st n}     → p ⊨ ((□ φ) ∧ (□ (φ ⇒ ψ)))
                                                ----------------------------
                                                → p ⊨ (□ ψ)



{-==============================
            THEOREMS
==============================-}


∧-comm : ∀ {n φ ψ l st}  {m : Stm* l st} {p : Prog m n} → p ⊨ (φ ∧ ψ) → p ⊨ (ψ ∧ φ)
∧-comm p = ∧-i (∧-e₂ p) (∧-e₁ p)

∧-trans : ∀ {n φ ψ χ l st} {m : Stm* l st} {p : Prog m n} → p ⊨ (φ ∧ ψ) → p ⊨ (ψ ∧ χ) → p ⊨ (φ ∧ χ)
∧-trans p q = ∧-i (∧-e₁ p) (∧-e₂ q)

∧⇒∨ : ∀ {l st n φ ψ} {m : Stm* l st} {p : Prog m n} → p ⊨ (φ ∧ ψ) → p ⊨ (φ ∨ ψ)
∧⇒∨ p = ∨-i₁ (∧-e₁ p)

□-∧-comm : ∀ {l st n φ ψ} {m : Stm* l st} {p : Prog m n} → p ⊨ □ (φ ∧ ψ) → p ⊨ □ (ψ ∧ φ)
□-∧-comm x = □-mod (∧-comm assume) x

□-∧-e₁ : ∀ {l st n φ ψ} {m : Stm* l st} {p : Prog m n} → p ⊨ □ (φ ∧ ψ) → p ⊨ (□ φ)
□-∧-e₁ x = □-mod (∧-e₁ assume) x

□-∧-e₂ : ∀ {l st n φ ψ} {m : Stm* l st} {p : Prog m n} → p ⊨ □ (φ ∧ ψ) → p ⊨ (□ ψ)
□-∧-e₂ x = □-mod (∧-e₂ assume) x


□-∧-exp : ∀ {l n φ ψ st} {st* : Stm* l st} {p : Prog st* n} → p ⊨ (□ (φ ∧ ψ)) → p ⊨ ((□ φ) ∧ (□ ψ))
□-∧-exp x = ∧-i (□-∧-e₁ x) (□-∧-e₂ x)

◇-∧-e₁ : ∀ {l n φ ψ st} {st* : Stm* l st} {p : Prog st* n} → p ⊨ ◇ (φ ∧ ψ) → p ⊨ ◇ φ
◇-∧-e₁ x = ◇-mod (∧-e₁ assume) x

◇-∧-e₂ : ∀ {l n φ ψ st} {st* : Stm* l st} {p : Prog st* n} → p ⊨ ◇ (φ ∧ ψ) → p ⊨ ◇ ψ
◇-∧-e₂ x = ◇-mod (∧-e₂ assume) x

◇-∧-exp : ∀ {l n φ ψ st} {st* : Stm* l st} {p : Prog st* n} → p ⊨ (◇ (φ ∧ ψ)) → p ⊨ ((◇ φ) ∧ (◇ ψ))
◇-∧-exp x = ∧-i (◇-∧-e₁ x) (◇-∧-e₂ x)

∨-comm : ∀ {l st n φ ψ} {m : Stm* l st} {p : Prog m n} → p ⊨ (φ ∨ ψ) → p ⊨ (ψ ∨ φ)
∨-comm p = ∨-e p (∨-i₂ assume) (∨-i₁ assume)

⇒-trans : ∀ {l st n φ ψ χ} {m : Stm* l st} {p : Prog m n} → p ⊨ (φ ⇒ ψ) → p ⊨ (ψ ⇒ χ) → p ⊨ (φ ⇒ χ)
⇒-trans p q = ⇒-i (⇒-e (weak q) (⇒-e (weak p) assume))

~>-t : ∀ {l st n φ ψ χ} {m : Stm* l st} {p : Prog m n}→ p ⊨ (φ ~> ψ) → p ⊨ (ψ ~> χ) → p ⊨ (φ ~> χ)
~>-t p q = □-~> (□-⇒-i (⇒-e (□-e (~>-□ (weak q))) (⇒-e (□-e (weak (~>-□ p))) assume)))

~>-refl : ∀ {l st n φ} {m : Stm* l st} {p : Prog m n} → p ⊨ (φ ~> φ)
~>-refl = □-~> (□-⇒-i assume)

~>-e : ∀ {l st n φ ψ} {m : Stm* l st} {p : Prog m n} → p ⊨ (φ ~> ψ) → p ⊨ ◇ φ → p ⊨ ◇ ψ
~>-e p q = ⇒-e (□-e (~>-□ p)) q

:=n-step : ∀ {n l a x v st} {m : Stm* l st} {p : Prog m n} → Stm* a (x :=n v) → p ⊨ (at a ~> af a)
:=n-step x = ~>-∧-e₁ (:=n-R x)

:=b-T-step : ∀ {n l a x st} {m : Stm* l st} {p : Prog m n} → Stm* a (x :=b (bool true)) → p ⊨ (at a ~> af a)
:=b-T-step x = ~>-∧-e₁ (:=b-T-R x)

:=b-F-step : ∀ {n l a x st} {m : Stm* l st} {p : Prog m n} → Stm* a (x :=b (bool false)) → p ⊨ (at a ~> af a)
:=b-F-step x = ~>-∧-e₁ (:=b-F-R x)

□-◇ : ∀ {l st n φ} {m : Stm* l st} {p : Prog m n} → p ⊨ □ φ → p ⊨ ◇ φ
□-◇ p = ◇-i (□-e p)
