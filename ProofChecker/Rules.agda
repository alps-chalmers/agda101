{-
  Contains rules to use when construction proofs. Also has functions to check if rules are used legally
-}
module Rules where

open import Translator
open import LTL
open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Label
open import ValidProof
open import Data.String as String
open import Data.Nat.Show as Show
open import LTLRule

{-used for convenience simple equal checker for nats-}
_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' suc y = false
suc x ==' zero = false
suc x ==' suc y = x ==' y

-- Index with rule and ltl. Specifically for proofsteps regarding the program itself
data ProgRule : LTL → Action → Set where
  assRule   : (φ : LTL) → ProgRule φ assign
  parRule   : (φ : LTL) → ProgRule φ par
  seqRule   : (φ : LTL) → ProgRule φ seq
  whileRule : (φ : LTL) → ProgRule φ while
  orRule    : (φ : LTL) → ProgRule φ or'
  inInf     : (φ : LTL) → ProgRule φ while
  atomLive  : (φ : LTL) → ProgRule φ flowA
  exitRule  : (φ : LTL) → ProgRule φ while

{-our different rules - program rules, ltl-rules and custom rules (forced truths)-}
data Rule : Set where
  progR   : {a : Action } {φ : LTL} → ProgRule φ a → Rule
  ltlR    : LTLRule → Rule
  customR : ℕ → LTL → LTL → Rule

{-to string for rules-}
pRule : Rule → String
pRule (progR (assRule φ)) = "assRule"
pRule (progR (parRule φ)) = "parRule"
pRule (progR (seqRule φ)) = "seqRule"
pRule (progR (whileRule φ)) = "whileRule"
pRule (progR (orRule φ)) = "orRule"
pRule (progR (inInf φ)) = "inInf"
pRule (progR (atomLive φ)) = "atomLive"
pRule (progR (exitRule φ)) = "exitRule"
pRule (ltlR ∧-e₁) = "∧-e₁"
pRule (ltlR ∧-e₂) = "∧-e₂"
pRule (ltlR (∨-i₁ x)) = "∨-i₁"
pRule (ltlR (∨-i₂ x)) = "∨-i₂"
pRule (customR x x₁ x₂) = "Custom " String.++ Show.show x

{-to string for LTL-}
pLTL : LTL → String
pLTL T' = "T'"
pLTL ⊥ = "⊥"
pLTL (∼ x) = "(∼ " String.++ (pLTL x) String.++ ")"
pLTL (□ x) = "(□ " String.++ (pLTL x) String.++ ")"
pLTL (◇ x) = "(◇ " String.++ (pLTL x) String.++ ")"
pLTL (x ∧' x₁) = "(" String.++ (pLTL x) String.++ " ∧' " String.++ (pLTL x₁) String.++ ")"
pLTL (x ∨' x₁) = "(" String.++ (pLTL x) String.++ " ∨' " String.++ (pLTL x₁) String.++ ")"
pLTL (x ⇒ x₁) = "(" String.++ (pLTL x) String.++ " ⇒ " String.++ (pLTL x₁) String.++ ")"
pLTL (x ~> x₁) = "(" String.++ (pLTL x) String.++ " ~≳ " String.++ (pLTL x₁) String.++ ")"
pLTL (x EQ x₁) = "(" String.++ (Show.show x) String.++ " EQ " String.++ (Show.show x₁) String.++ ")"
pLTL (at (s x)) = "(at " String.++ (Show.show x) String.++ ")"
pLTL (in' (s x)) = "(in " String.++ (Show.show x) String.++ ")"
pLTL (after (s x)) = "(after " String.++ (Show.show x) String.++ ")"
pLTL (isTrue x) = "(isTrue " String.++ (Show.show x) String.++ ")"

{-Checks if LTL statements are identical-}
isEq : (φ : LTL) → (ψ : LTL) → Bool
isEq T' T' = true
isEq ⊥ ⊥ = true
isEq (∼ x) (∼ y) = isEq x y
isEq (□ x) (□ y) = isEq x y
isEq (◇ x) (◇ y) = isEq x y
isEq (x₁ ∧' x₂) (y₁ ∧' y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ∨' x₂) (y₁ ∨' y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ⇒ x₂) (y₁ ⇒ y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ~> x₂) (y₁ ~> y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (at (s x)) (at (s y)) = x ==' y
isEq (after (s x)) (after (s y)) = x ==' y
isEq (x₁ EQ x₂) (y₁ EQ y₂) = ((x₁ ==' y₁)) ∧ (x₂ ==' y₂)
isEq _ _ = false

{-Checks if actions are identical-}
isEqA : Action → Action → Bool
isEqA assign assign = true
isEqA par par = true
isEqA seq seq = true
isEqA while while = true
isEqA or' or' = true
isEqA inInf inInf = true
isEqA flowA flowA = true
isEqA _ _ = false

{-Checks if a program rule is applied in a legal way-}
legalApplication : {φ : LTL} {a : Action} → List TransRel → LTL → ProgRule φ a → ValidProof
legalApplication {φ} {a} [] ψ pr = no ((pLTL φ) String.++ " not found when applying " String.++ (pRule (progR pr)) String.++ " to " String.++ (pLTL ψ))
legalApplication {a} (todo ∷ rels) ψ pr = legalApplication rels ψ pr
legalApplication {φ} {a} (< pre > a' < post > ∷ rels) ψ pr = if isEq pre ψ ∧ isEqA a a' then yes post else legalApplication rels ψ pr

{-Checks if an LTL-rule is applied in a legal way-}
applyLTL-R : LTL → LTLRule → ValidProof
applyLTL-R (φ ∧' ψ) ∧-e₁ = yes φ
applyLTL-R (φ ∧' ψ) ∧-e₂ = yes ψ
applyLTL-R φ (∨-i₁ ψ) = yes (ψ ∨' φ)
applyLTL-R φ (∨-i₂ ψ) = yes (φ ∨' ψ)
applyLTL-R φ r = no ((pRule (ltlR r)) String.++ " cannot be applied to " String.++ (pLTL φ))

{-General application function. Takes a translated program, a thruth and a rule. Returns if it is a Valid proof-}
applyRule : List TransRel → LTL → Rule → ValidProof
applyRule ts φ (progR x) = legalApplication ts φ x
applyRule ts φ (ltlR r) = applyLTL-R φ r
applyRule ts φ (customR n pre post) = if (isEq pre φ) then yes post else no err
  where err = "The custom rule " String.++ (pRule (customR n pre post)) String.++ " cannot be applied to" String.++ (pLTL φ)
