module Proof where

open import LTL
open import Rules
open import Tree
open import Bool

data ProofStep : Set where
  step : LTL -> Rule -> ProofStep

data Proof : Set where
  proof : Tree ProofStep -> Proof


prove : Proof -> Bool
prove (proof (leaf x)) = {!   !}
prove (proof (branch x y z)) = {! if x is fine then prove y and prove   !}
