module Translator where

open import Program
open import Lists
open import MapFold
open import Label
open import LTL

data Entails : Set where
  xD  : Entails
  _⊢_ : (c₁ : LTL) → (c₂ : LTL) → Entails


transStm : Label → Stm → Entails
transStm l < x >:=n< x₁ > = xD
transStm l < (vN x) :=n nat n > = at l ⊢ ((after l) ∧ (x EQ n))
transStm l < x :=n nVar x₁ > = xD -- {!   !} ⊢ ((after l) ∧ ({!   !} EQ {!   !}))
transStm l < x >:=b< x₁ > = xD
transStm l < x :=b x₁ > = xD
transStm l (wait x) = xD

{-# TERMINATING #-}

translate' : Seg → List Entails
translate' (seg x stm) = (transStm x stm) :: empty
translate' (block xs) = foldl (λ ls se → (translate' se) ++ ls) empty xs
translate' (par x xs) = foldl (λ ls se → (translate' se) ++ ls) empty xs
translate' (while x x₁ se) = empty
translate' (if x x₁ se) = empty

translate : Prog → List Entails
translate (prog init main) = translate' main
