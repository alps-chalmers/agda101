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

_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' suc y = false
suc x ==' zero = false
suc x ==' suc y = x ==' y

-- Index with rule and ltl
data ProgRule : LTL → Action → Set where
  assRule   : (φ : LTL) → ProgRule φ assign
  parRule   : (φ : LTL) → ProgRule φ par
  seqRule   : (φ : LTL) → ProgRule φ flowA
  whileRule : (φ : LTL) → ProgRule φ while
  orRule    : (φ : LTL) → ProgRule φ or'
  inInf     : (φ : LTL) → ProgRule φ while
  atomLive  : (φ : LTL) → ProgRule φ flowA
  exitRule  : (φ : LTL) → ProgRule φ while


data Rule : Set where
  progR   : {a : Action } {φ : LTL} → ProgRule φ a → Rule
  ltlR    : LTLRule → Rule
  customR : ℕ → LTL → LTL → Rule

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

data Ru : LTL → Set where
  id    : (φ : LTL) → Ru φ
  ∧'-i   : {φ ψ : LTL} → Ru φ → Ru ψ → Ru (φ ∧' ψ)
  ∧'-e₁  : {φ ψ : LTL} → Ru (φ ∧' ψ) → Ru φ
  inInf : {l : Label} → Ru (in' l) → Ru ((at l) ∨' (after l))

data Valid : Set where
  yes : {φ : LTL} → Ru φ → Valid
  no  : Valid -- TODO Add error' message

extract : {φ : LTL} → Ru φ → LTL
extract {φ} _ = φ

f : (φ : LTL) → Ru φ
f x = id x

r-∧'-i : {φ ψ : LTL} → Ru (φ) → Ru (ψ) → Valid
r-∧'-i r₁ r₂ = yes (∧'-i r₁ r₂)

r-∧'-e₁ : LTL → Valid
r-∧'-e₁ (φ ∧' ψ) = yes (∧'-e₁ (id (φ ∧' ψ)))
r-∧'-e₁ _ = no


test : Valid
test = r-∧'-e₁ (extract (id (at (s 0))))

r-inInf : LTL → Valid
r-inInf (in' l) = yes (inInf (id (in' l)))
r-inInf _ = no

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

isEqA : Action → Action → Bool
isEqA assign assign = true
isEqA par par = true
isEqA seq seq = true
isEqA while while = true
isEqA or' or' = true
isEqA dummy dummy = true
isEqA inInf inInf = true
isEqA □-e □-e = true
isEqA flowA flowA = true
isEqA (custom x) (custom y) = x ==' y
isEqA _ _ = false

legalApplication : {φ : LTL} {a : Action} → List TransRel → ProgRule φ a → ValidProof
legalApplication {φ} {a} [] pr = no ((pLTL φ) String.++ " not found.")
legalApplication {a} (todo ∷ rels) pr = legalApplication rels pr
legalApplication {φ} {a} (< pre > a' < post > ∷ rels) pr = if isEq pre φ ∧ isEqA a a' then yes post else legalApplication rels pr


applyLTL-R : LTL → LTLRule → ValidProof
applyLTL-R (φ ∧' ψ) ∧-e₁ = yes φ
applyLTL-R (φ ∧' ψ) ∧-e₂ = yes ψ
applyLTL-R φ (∨-i₁ ψ) = yes (ψ ∨' φ)
applyLTL-R φ (∨-i₂ ψ) = yes (φ ∨' ψ)
applyLTL-R _ _ = no "Incorrect LTL application."

applyRule : List TransRel → LTL → Rule → ValidProof
applyRule ts φ (progR x) = legalApplication ts x
applyRule ts φ (ltlR r) = applyLTL-R φ r
applyRule ts φ (customR n pre post) = if (isEq pre φ) then yes post else no ("The custom rule could not be applied")
