module LTL where

open import Label
open import Data.String
open import Data.Nat

-- The extended LTL data type
data LTL : Set where
  T ⊥           : LTL                                -- true & false
  ∼             : (φ : LTL) → LTL                    -- not
  □ ◇           : (φ : LTL) → LTL                    -- always & eventually
  _∧_ _∨_       : (φ : LTL) → LTL → LTL              -- and & or
  _⇒_           : (φ : LTL) → LTL → LTL              -- implies
  _~>_          : (φ : LTL) → (ψ : LTL) → LTL        -- leads to - (P ~> Q) ≡ □(P ⊂ ◇Q)
  at in' after  : (l : Label) → LTL                  -- at, in & after a code segment - extended
                                                    -- from Owiki & Lamport
  _==n_         : (x : String) → (n : ℕ) → LTL       -- Nat variable x has the value n
  _==b_         : (x : String) → (y : String) → LTL  -- Bool variable x has the value of y
  isTrue        : (x : String) → LTL                 -- Variable x has the value -- true
