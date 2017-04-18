module ProofBuilder where

open import Proof
open import Program
open import Label
open import LTL

-- TODO
-- * Index Label over ℕ
-- * Fix fin
-- * Implement if/while


{- Program representation -}
s0 : Stm (s 0) ("x" := 0) (s 1)
s0 = reg (s 0) ("x" := 0) (s 1)

s1 : Stm (s 1) ("x" := 1) (s 2)
s1 = reg (s 1) ("x" := 1) (s 2)

s3 : Stm (s 3) ("x" := 5) (fin (s 3))
s3 = reg (s 3) ("x" := 5) (fin (s 3))

s4 : Stm (s 4) ("x" := 6) (fin (s 4))
s4 = reg (s 4) ("x" := 6) (fin (s 4))

s2 : Stm (s 2) ((s 3) || (s 4)) (fin (s 2))
s2 = par (s 2) s3 s4 (fin (s 2))

{- Proof for the program. -}

s0=>s1 : Proof (at (s 0)) → Proof (at (s 1))
s0=>s1 p = flow ( ∧-e₁ (assiRule p s0)) s0

s1=>s2 : Proof (at (s 1)) → Proof (at (s 2))
s1=>s2 p = flow ( ∧-e₁ (assiRule p s1)) s1

s2=>s3 : Proof (at (s 2)) → Proof (at (s 3))
s2=>s3 p =  ∧-e₁ (parRule p s2)

s2=>s4 : Proof (at (s 2)) → Proof (at (s 4))
s2=>s4 p =  ∧-e₂ (parRule p s2)

s3=>s3' : Proof (at (s 3)) → Proof (after (s 3))
s3=>s3' p =  ∧-e₁ (assiRule p s3)

s4=>s4' : Proof (at (s 4)) → Proof (after (s 4))
s4=>s4' p =  ∧-e₁ (assiRule p s4)

s2=>s3'∧s4' : Proof (at (s 2)) → Proof ((after (s 3)) ∧' (after (s 4)))
s2=>s3'∧s4' p = ∧-i (s3=>s3' (s2=>s3 p)) (s4=>s4' (s2=>s4 p))

s2=>s2' : Proof (at (s 2)) → Proof (after (s 2))
s2=>s2' p =  ∧-e₁ (exitPar (s2=>s3'∧s4' p) s2)

-- Final proof of termination
proof : Proof (at (s 0)) → Proof (after (s 2))
proof p = s2=>s2' (s1=>s2 (s0=>s1 p))
