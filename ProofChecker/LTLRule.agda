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
  ∧-e₁  : LTLRule        -- and-elimination on first element
  ∧-e₂  : LTLRule        -- and-elimination on second element
  ∨-i₁  : LTL → LTLRule  -- or-elimination on first element
  ∨-i₂  : LTL → LTLRule  -- or-elimination on second element
