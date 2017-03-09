module Translator where

open import Program
open import Lists
open import MapFold
open import Label
open import LTL

data Action : Set where
  assign : Action

data TransRel : Set where
  xD  : TransRel
  [_]_[_] : (c₁ : LTL) → Action → (c₂ : LTL) → TransRel

transStm : Label → Stm → TransRel
transStm l < x >:=n< x₁ > = xD
transStm l < (vN x) :=n nat n > = [ at l ] assign [ (after l) ∧ (x EQ n) ]
transStm l < x :=n nVar x₁ > = xD -- {!   !} entails ((after l) ∧ ({!   !} EQ {!   !}))
transStm l < x >:=b< x₁ > = xD
transStm l < x :=b x₁ > = xD
transStm l (wait x) = xD

{-# TERMINATING #-}

translate' : Seg → List TransRel
translate' (seg x stm) = (transStm x stm) :: empty
translate' (block xs) = foldl (λ ls se → (translate' se) ++ ls) empty xs
translate' (par x xs) = foldl (λ ls se → (translate' se) ++ ls) empty xs
translate' (while x x₁ se) = empty
translate' (if x x₁ se) = empty

translate : Prog → List TransRel
translate (prog init main) = translate' main
