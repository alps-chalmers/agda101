module ELTL where

open import Data.Nat
open import Data.Bool as Bool using (Bool; true; false)
open import Data.String

infixl 6 T ⊥ _==n_ _==b_ at in' after
infixl 7 □ ◇
infixl 8 ∼
infixl 9 _∨_ _∧_
infixl 10 _⇒_ _~>_

-- ℕ extended with variables.
data ℕ* : Set where
  nat  : (n : ℕ) → ℕ*
  var  : (x : String) → ℕ*
  _+*_ : (n₁ n₂ : ℕ*) → ℕ*
  _-*_ : (n₁ n₂ : ℕ*) → ℕ*
  _×*_ : (n₁ n₂ : ℕ*) → ℕ*

-- Bool extended with variables.
data Bool* : Set where
  var   : (x : String) → Bool*
  bool  : (b : Bool) → Bool*
  _<*_  : (x : ℕ*) → (y : ℕ*) → Bool*
  _<=*_ : (x : ℕ*) → (y : ℕ*) → Bool*
  _>*_  : (x : ℕ*) → (y : ℕ*) → Bool*
  _>=*_ : (x : ℕ*) → (y : ℕ*) → Bool*
  _==n_ : (x : String) → (n : ℕ*) → Bool*     -- Nat variable x has the value n
  _==b_ : (x : String) → (b : Bool*) → Bool*  -- Bool variable x has the value of y


{- a label is used as a reference to a code segment - see more in Program -}
data Label : Set where
  prc : (n : ℕ) -> Label
  s   : (n : ℕ) -> Label

-- The extended ELTL data type
data ELTL : Set where
  T ⊥           : ELTL                               -- true & false
  ∼             : (φ : ELTL) → ELTL                  -- not
  □ ◇           : (φ : ELTL) → ELTL                  -- always & eventually
  _∧_ _∨_       : (φ : ELTL) → ELTL → ELTL           -- and & or
  _⇒_           : (φ : ELTL) → ELTL → ELTL           -- implies
  _~>_          : (φ : ELTL) → (ψ : ELTL) → ELTL     -- leads to - (P ~> Q) ≡ □(P ⊂ ◇Q)
  at in' after  : (l : Label) → ELTL                 -- at, in & after a code segment - extended
  b*            : (b : Bool*) → ELTL
