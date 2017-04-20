{-
  LTL-rules, used when making a proofstep (see ProofChecker) that is regarding
  an LTL formulae.
-}

{-***** imported modules *****-}
module LTLRule where
open import LTL
{-****************************-}

-- The LTL-rule data type
data LTLRule : Set where
  ∧-e₁   : LTL → LTLRule        -- and-elimination on first element
  ∧-e₂   : LTL → LTLRule        -- and-elimination on second element
  ∧-i    : LTL → LTL → LTLRule  -- and-insertion on two LTL formulae
  ∨-i₁   : LTL → LTL → LTLRule  -- or-elimination on first element
  ∨-i₂   : LTL → LTL → LTLRule  -- or-elimination on second element
  ∨-e    : LTL → LTLRule
  □-e    : LTL → LTLRule
  □-∧-e₁ : LTL → LTLRule
  □-∧-e₂ : LTL → LTLRule
  exp-∧  : LTL → LTLRule
