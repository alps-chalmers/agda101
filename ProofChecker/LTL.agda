{-
  Extended LTL logic in order to reason properly about programs, used in
  Translator, LTLRule & Proofchecker
-}
module LTL where

{-***** imported modules *****-}
open import Label
open import Data.Nat
open import Data.Bool
open import Data.String
open import Data.Vec renaming (_++_ to _v++_)
open import Program
open import Data.Fin as Fin using (Fin; zero; suc; fromℕ)
{-****************************-}

-- The extended LTL data type
data LTL : Set where
  T' ⊥         : LTL                            -- true & false
  ∼            : (φ : LTL) → LTL                -- not
  □ ◇          : (φ : LTL) → LTL                -- always & eventually
  _∧'_ _∨'_    : (φ : LTL) → LTL → LTL          -- and & or
  _⇒_          : (φ : LTL) → LTL → LTL          -- implies
  _~>_         : (φ : LTL) → (ψ : LTL) → LTL    -- leads to - (P ~> Q) ≡ □(P ⊂ ◇Q)
  at in' after : (l : Label) → LTL              -- at, in & after a code segment - extended
                                                -- from Owiki & Lamport
  _==n_        : (x : NVar) → (n : ℕ) → LTL     -- Nat variable x has the value n
  _==b_        : (x : BVar) → (y : BVar) → LTL  -- Bool variable x has the value of y
  isTrue       : (x : BVar) → LTL               -- Variable x has the value -- true
