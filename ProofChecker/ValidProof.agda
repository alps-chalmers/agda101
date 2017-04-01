module ValidProof where

open import Data.String
open import LTL

data ValidProof : Set where
  yes : LTL → ValidProof
  no  : String → ValidProof
