module Rules where

open import Translator
open import LTL
open import Lists
open import Bool
open import Maybe
open import Nat
open import Label

data _⊢_ : LTL → LTL → Set where


-- Index with rule and ltl
data Rule : Set where
  assRule   : LTL → Rule
  parRule   : LTL → Rule
  seqRule   : LTL → Rule
  whileRule : LTL → Rule
  orRule    : LTL → Rule
  dummy     : LTL → Rule
  inInf     : LTL → Rule
  atomLive  : LTL → Rule
  customR   : Nat → LTL → Rule
  exitRule  : LTL → Rule
  □-e       : LTL → Rule
  ∧-e1      : LTL → Rule
  ∧-e2      : LTL → Rule
  ∧-i       : LTL → Rule


extLTL : Rule → LTL
extLTL (assRule φ) = φ
extLTL (parRule φ) = φ
extLTL (seqRule φ) = φ
extLTL (whileRule φ) = φ
extLTL (orRule φ) = φ
extLTL (dummy φ) = φ
extLTL (inInf φ) = φ
extLTL (□-e φ) = φ
extLTL (∧-e1 φ) = φ
extLTL (∧-e2 φ) = φ
extLTL (customR _ φ) = φ
extLTL (atomLive φ) = φ
extLTL (exitRule φ) = φ
extLTL (∧-i φ) = φ

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
legalApplication [] a l = Nothing
legalApplication (todo :: ts) a l = legalApplication ts a l
legalApplication ([ pre ] a' [ post ] :: ts) a l = if (isEq l pre) && isEqA a a' then Just post else legalApplication ts a l

extAction : Rule → Action
extAction (assRule _) = assign
extAction (parRule _) = par
extAction (seqRule _) = seq
extAction (whileRule _) = while
extAction (orRule _) = or
extAction (dummy _) = dummy
extAction (inInf _) = inInf
extAction (□-e _) = □-e
extAction (∧-e1 _) = ltl
extAction (∧-e2 _) = ltl
extAction (atomLive _) = ltl
extAction (exitRule _ ) = ltl
extAction (customR n _) = custom n
extAction (∧-i _) = ltl

applyRule : List TransRel → LTL → Rule → LTL
applyRule ts ls r with legalApplication ts (extAction r) (extLTL r)
... | Just post = if isEq (extLTL r) ls then post else ⊥
... | Nothing = ⊥

{-}
applyRule : List TransRel → LTL → Rule → LTL
applyRule ts ls (assRule φ) with legalApplication ts assign φ
... | Just post = if isEq φ ls then post else ⊥
... | Nothing = ⊥
applyRule ts ls (parRule φ) with legalApplication ts par φ
... | Just post = if isEq φ ls then post else ⊥
... | Nothing = ⊥
applyRule ts ls (seqRule φ) with legalApplication ts seq φ
... | Just post = if isEq φ ls then post else ⊥
... | Nothing = ⊥
-- applyRule ts ls (andRule1 (φ ∧ ψ)) = φ
-- applyRule ts ls (andRule2 (φ ∧ ψ)) = ψ
-- applyRule _ _ _ = ⊥
-}
