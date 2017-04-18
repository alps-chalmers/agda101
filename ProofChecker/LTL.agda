{-
  Extended LTL logic in order to reason properly about programs, used in
  Translator, LTLRule & Proofchecker
-}
module LTL where

{-***** imported modules *****-}
open import Label
open import Data.Nat
open import Data.Nat.Show as Show
open import Data.Bool
open import Data.String renaming (_++_ to _s++_)
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

{-
  to string for LTL formulae, self explanatory
-}
pLTL : LTL → String
pLTL T' = "T'"
pLTL ⊥ = "⊥"
pLTL (∼ x) = "(∼ " s++ (pLTL x) s++ ")"
pLTL (□ x) = "(□ " s++ (pLTL x) s++ ")"
pLTL (◇ x) = "(◇ " s++ (pLTL x) s++ ")"
pLTL (x ∧' x₁) = "(" s++ (pLTL x) s++ " ∧' " s++ (pLTL x₁) s++ ")"
pLTL (x ∨' x₁) = "(" s++ (pLTL x) s++ " ∨' " s++ (pLTL x₁) s++ ")"
pLTL (x ⇒ x₁) = "(" s++ (pLTL x) s++ " ⇒ " s++ (pLTL x₁) s++ ")"
pLTL (x ~> x₁) = "(" s++ (pLTL x) s++ " ~≳ " s++ (pLTL x₁) s++ ")"
pLTL (x ==n y) = "(" s++ pExpN (nVar x) s++ " == " s++ (Show.show y) s++ ")"
pLTL (vB x ==b vB y) = "(" s++ x s++ " == " s++ y s++ ")"
pLTL (at (s x)) = "(at " s++ (Show.show x) s++ ")"
pLTL (in' (s x)) = "(in " s++ (Show.show x) s++ ")"
pLTL (after (s x)) = "(after " s++ (Show.show x) s++ ")"
pLTL (isTrue (vB x)) = "(isTrue " s++ x s++ ")"

{-
  Used for convenience, simple equal checker for ℕ, self explanatory
-}
_=='_ : ℕ → ℕ → Bool
0 ==' 0 = true
0 ==' (suc y) = false
suc x ==' 0 = false
suc x ==' suc y = x ==' y

{-
  Checks if LTL statements are identical, self explanatory
-}
isEq : (φ : LTL) → (ψ : LTL) → Bool
isEq T' T' = true
isEq ⊥ ⊥ = true
isEq (∼ x) (∼ y) = isEq x y
isEq (□ x) (□ y) = isEq x y
isEq (◇ x) (◇ y) = isEq x y
isEq (x₁ ∧' x₂) (y₁ ∧' y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ∨' x₂) (y₁ ∨' y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ⇒ x₂) (y₁ ⇒ y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (x₁ ~> x₂) (y₁ ~> y₂) = (isEq x₁ y₁) ∧ ((isEq x₂ y₂))
isEq (at (s x)) (at (s y)) = x ==' y
isEq (after (s x)) (after (s y)) = x ==' y
isEq (vN x ==n n₁) (vN y ==n n₂) = (x == y) ∧ (n₁ ==' n₂)
isEq (vB x ==b vB x₁) (vB x₂ ==b vB x₃) = (x == x₂) ∧ (x₁ == x₃)
isEq (isTrue (vB x)) (isTrue (vB y)) = x == y
isEq _ _ = false
