{-
  Contains rules to use when construction proofs. Also has functions to check if
  rules are used legally. Used in ProofChecker
-}
module Rules where

{-***** imported modules *****-}
open import Translator
open import LTL
open import Data.List
open import Data.Bool
open import Data.Maybe
open import Data.Nat
open import Label
open import ValidProof
open import Data.String as String renaming (_++_ to _s++_)
open import Data.Nat.Show as Show
open import LTLRule
open import Program
{-****************************-}

{-
  Used for convenience, simple equal checker for ℕ, self explanatory
-}
_=='_ : ℕ → ℕ → Bool
0 ==' 0 = true
0 ==' (suc y) = false
suc x ==' 0 = false
suc x ==' suc y = x ==' y

{-
  Data type for program rules, indexed with rule and ltl. Specifically for
  proofsteps regarding the programs
-}
data ProgRule : LTL → Action → Set where
  assRule   : (φ : LTL) → ProgRule φ assign  -- Assignment rule
  parRule   : (φ : LTL) → ProgRule φ par     -- Parallel rule
  seqRule   : (φ : LTL) → ProgRule φ seq     -- Sequential rule, used for
                                             -- entering non-basic segments (see
                                             -- Program)
  whileRule : (φ : LTL) → ProgRule φ while   -- While loop rule
  orRule    : (φ : LTL) → ProgRule φ or'     -- Or rule, used when making a
                                             -- branch
  inInf     : (φ : LTL) → ProgRule φ while   -- TODO
  atomLive  : (φ : LTL) → ProgRule φ flowA   -- Atomic liveness rule used to
                                             -- control progression
  exitRule  : (φ : LTL) → ProgRule φ while   -- Used when leaving a while loop

{-
  our different rules - program rules, ltl-rules and custom rules (forced
  truths)
-}
data Rule : Set where
  progR   : {a : Action } {φ : LTL} → ProgRule φ a → Rule  -- Program rule
  ltlR    : LTLRule → Rule                                 -- LTL rule
  customR : ℕ → LTL → LTL → Rule                           -- Custom rule

{-
  To-string for rules, self explanatory
-}
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
pRule (customR x x₁ x₂) = "Custom " s++ Show.show x

pExpN : ExpN → String
pExpN (nat x) = Show.show x
pExpN (nVar (vN x)) = x

{-
  to string for LTL formulae, self explanatory
-}
pLTL : LTL → String
pLTL T' = "T'"
pLTL ⊥ = "⊥"
pLTL (∼ x) = "(∼ " s++ (pLTL x) s++ ")"
pLTL (□ x) = "(□ " s++ (pLTL x) s++ ")"
pLTL (◇ x) = "(◇ " s++ (pLTL x) s++ ")"
pLTL (x ∧' x₁) = "(" s++ (pLTL x) s++ " ∧' " s++ (pLTL x₁) s++ ")"
pLTL (x ∨' x₁) = "(" s++ (pLTL x) s++ " ∨' " s++ (pLTL x₁) s++ ")"
pLTL (x ⇒ x₁) = "(" s++ (pLTL x) s++ " ⇒ " s++ (pLTL x₁) s++ ")"
pLTL (x ~> x₁) = "(" s++ (pLTL x) s++ " ~≳ " s++ (pLTL x₁) s++ ")"
pLTL (x ==n y) = "(" s++ pExpN (nVar x) s++ " == " s++ (Show.show y) s++ ")"
pLTL (vB x ==b vB y) = "(" s++ x s++ " == " s++ y s++ ")"
pLTL (at (s x)) = "(at " s++ (Show.show x) s++ ")"
pLTL (in' (s x)) = "(in " s++ (Show.show x) s++ ")"
pLTL (after (s x)) = "(after " s++ (Show.show x) s++ ")"
pLTL (isTrue (vB x)) = "(isTrue " s++ x s++ ")"
--

{-
  Checks if LTL statements are identical, self explanatory
-}
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
isEq (vN x ==n n₁) (vN y ==n n₂) = (x == y) ∧ (n₁ ==' n₂)
isEq (vB x ==b vB x₁) (vB x₂ ==b vB x₃) = (x == x₂) ∧ (x₁ == x₃)
isEq _ _ = false

{-
  Checks if actions are identical, self explanatory
-}
isEqA : Action → Action → Bool
isEqA assign assign = true
isEqA par par = true
isEqA seq seq = true
isEqA while while = true
isEqA or' or' = true
isEqA inInf inInf = true
isEqA flowA flowA = true
isEqA _ _ = false

{-
  Checks if a program rule is applied in a legal way
  legalApplication : program translation → LTL formula → rule to apply on the
  LTL formula → valid proof
-}
legalApplication : {φ : LTL} {a : Action} → List TransRel → LTL → ProgRule φ a → ValidProof
legalApplication {φ} {a} [] ψ pr = no ((pLTL φ) s++ " not found when applying " s++ (pRule (progR pr)) s++ " to " s++ (pLTL ψ))
  -- If passed an empty program, return that it's invalid with an error message
legalApplication {φ} {a} (< pre > a' < post > ∷ rels) ψ pr = if isEq pre ψ ∧ isEqA a a' then yes post else legalApplication rels ψ pr
  -- If a triple (see Translator) is in the translation, its precondition is
  -- identical to the LTL formula and its action is identical to the rule's
  -- action, return that it's a valid proof for the postcondition. Else continue

{-
  Checks if an LTL-rule is applied in a legal way
  applyLTL-R : LTL formula → LTL rule → valid proof
-}
applyLTL-R : LTL → LTLRule → ValidProof
applyLTL-R (φ ∧' ψ) ∧-e₁ = yes φ      -- and elimination (see LTLRules)
applyLTL-R (φ ∧' ψ) ∧-e₂ = yes ψ      -- and elimination (see LTLRules)
applyLTL-R φ (∨-i₁ ψ) = yes (ψ ∨' φ)  -- or insertion (see LTLRules)
applyLTL-R φ (∨-i₂ ψ) = yes (φ ∨' ψ)  -- or insertion (see LTLRules)
applyLTL-R φ r = no ((pRule (ltlR r)) s++ " cannot be applied to " s++ (pLTL φ))                          -- anything else is invalid with a message

{-
  General application function. Takes a translated program, a thruth and a rule.
  Returns if it is a Valid proof
-}
applyRule : List TransRel → LTL → Rule → ValidProof
applyRule ts φ (progR x) = legalApplication ts φ x
  -- If the passed rule is a program rule, pass on to legalApplication and
  -- return the result
applyRule ts φ (ltlR r) = applyLTL-R φ r
  -- If the passed rule is an LTL rule, pass on to applyLTL-R and rreturn the
  -- result
applyRule ts φ (customR n pre post) = if (isEq pre φ) then yes post else no err
  where err = "The custom rule " s++ (pRule (customR n pre post)) s++ " cannot be applied to" s++ (pLTL φ)
  -- If the passed rule is a custom rule and if the precondition of the rule and
  -- the true LTL are identical, return that it's valid, else that it's invalid
