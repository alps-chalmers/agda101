{-
  Extended LTL logic in order to reason properly about programs, used in 
  Translator, LTLRule & Proofchecker
-}
module LTL where

{-***** imported modules *****-}
open import Label
open import Data.Nat
open import Data.Bool
{-****************************-}

-- The extended LTL data type
data LTL : Set where
  T' ⊥         : LTL              -- true & false
  ∼            : LTL → LTL        -- not
  □ ◇          : LTL → LTL        -- always & eventually
  _∧'_ _∨'_    : LTL → LTL → LTL  -- and & or
  _⇒_          : LTL → LTL → LTL  -- implies
  _~>_         : LTL → LTL → LTL  -- leads to - (P ~> Q) ≡ □(P ⊂ ◇Q)
  at in' after : Label → LTL      -- at, in & after a code segment - extended
                                  -- from Owiki & Lamport
  _EQ_         : ℕ → ℕ → LTL      -- Variable with number n has the value m
  isTrue       : ℕ → LTL          -- Variable with the number n has the value
                                  -- true
