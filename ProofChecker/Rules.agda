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

_=='_ : ℕ → ℕ → Bool
zero ==' zero = true
zero ==' suc y = false
suc x ==' zero = false
suc x ==' suc y = x ==' y

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
  customR   :  ℕ → LTL → Rule
  exitRule  : LTL → Rule
  □-e       : LTL → Rule
  ∧'-e1      : LTL → Rule
  ∧'-e2      : LTL → Rule
  ∧'-i       : LTL → Rule

pRule : Rule → String
pRule (assRule x) = "assRule"
pRule (parRule x) = "parRule"
pRule (seqRule x) = "seqRule"
pRule (whileRule x) = "whileRule"
pRule (orRule x) = "orRule"
pRule (dummy x) = "dummy"
pRule (inInf x) = "inInf"
pRule (atomLive x) = "atomLive"
pRule (customR x x₁) = "customR"
pRule (exitRule x) = "exitRule"
pRule (□-e x) = "□-e"
pRule (∧'-e1 x) = "∧'-e1"
pRule (∧'-e2 x) = "∧'-e2"
pRule (∧'-i x) = "∧'-i"
-- Add action reference

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
pLTL (in' (s x)) = "(at " String.++ (Show.show x) String.++ ")"
pLTL (after (s x)) = "(at " String.++ (Show.show x) String.++ ")"
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

{-test : (φ : LTL) → Ru (φ ∧' φ)
test x = r-∧'-i (id x) (id x)-}

r-inInf : LTL → Valid
r-inInf (in' l) = yes (inInf (id (in' l)))
r-inInf _ = no

extLTL : Rule → LTL
extLTL (assRule φ) = φ
extLTL (parRule φ) = φ
extLTL (seqRule φ) = φ
extLTL (whileRule φ) = φ
extLTL (orRule φ) = φ
extLTL (dummy φ) = φ
extLTL (inInf φ) = φ
extLTL (□-e φ) = φ
extLTL (∧'-e1 φ) = φ
extLTL (∧'-e2 φ) = φ
extLTL (customR _ φ) = φ
extLTL (atomLive φ) = φ
extLTL (exitRule φ) = φ
extLTL (∧'-i φ) = φ

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
isEqA seq sewq = true
isEqA _ _ = false

legalApplication : List TransRel → Action → LTL → ValidProof
legalApplication [] a l = no ((pLTL l) String.++ " not found.")
legalApplication (todo ∷ ts) a l = legalApplication ts a l
legalApplication (< pre > a' < post > ∷ ts) a l = if (isEq l pre) ∧ isEqA a a' then yes post else legalApplication ts a l

extAction : Rule → Action
extAction (assRule _) = assign
extAction (parRule _) = par
extAction (seqRule _) = seq
extAction (whileRule _) = while
extAction (orRule _) = or'
extAction (dummy _) = dummy
extAction (inInf _) = inInf
extAction (□-e _) = □-e
extAction (∧'-e1 _) = ltl
extAction (∧'-e2 _) = ltl
extAction (atomLive _) = ltl
extAction (exitRule _ ) = ltl
extAction (customR n _) = custom n
extAction (∧'-i _) = ltl

applyRule : List TransRel → LTL → Rule → ValidProof
applyRule ts ls r with legalApplication ts (extAction r) (extLTL r)
... | yes post = if isEq (extLTL r) ls then yes post else no eMsg
  where eMsg = ("The rule " String.++ pRule r String.++ (" could not be applied to the formula: " String.++ pLTL (extLTL r)))
... | err = err 
