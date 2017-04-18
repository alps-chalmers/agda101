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
--open import ValidProof
open import Data.String as String renaming (_++_ to _s++_)
open import Data.Nat.Show as Show
open import LTLRule
open import Program
{-****************************-}

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
pRule (ltlR (∧-e₁ _)) = "∧-e₁"
pRule (ltlR (∧-e₂ _)) = "∧-e₂"
pRule (ltlR (∨-i₁ _ _)) = "∨-i₁"
pRule (ltlR (∨-i₂ _ _)) = "∨-i₂"
pRule (ltlR (exp-∧ _)) = "exp-∧"
pRule (ltlR (∨-e _)) = "∨-e"
pRule (customR x x₁ x₂) = "Custom " s++ Show.show x
