{-
  Module for valid proofs. Tells if a proofstep/proof (see ProofChecker) is 
  valid or not. Used in ProofChecker
-}
module ValidProof where

{-***** imported modules *****-}
open import Data.String
open import Truths
{-****************************-}

{-
  Data type for valid proofs, either it is and is the valid LTL or it is not and
  is invalid with a message
-}
data ValidProof : Set where
  yes : Truths → ValidProof     -- Valid
  no  : String → ValidProof  -- Invalid
