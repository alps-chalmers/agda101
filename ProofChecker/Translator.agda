module Translator where

open import Program
open import Lists
open import MapFold
open import Label
open import LTL
open import Maybe
open import Nat
open import Bool

data Action : Set where
  assign : Action
  par    : Action
  seq    : Action
  while  : Action
  or     : Action
  dummy  : Action
  inInf  : Action
  □-e    : Action
  ltl    : Action
  custom : Nat → Action

data TransRel : Set where
  todo  : TransRel
  [_]_[_] : (c₁ : LTL) → Action → (c₂ : LTL) → TransRel

transStm : Label → Stm → TransRel
transStm l < x >:=n< x₁ > = todo
transStm l < (vN x) :=n nat n > = [ at l ] assign [ (after l) ∧ (x EQ n) ]
transStm l < x :=n nVar x₁ > = todo
transStm l < x >:=b< x₁ > = todo
transStm l < vB i :=b bool x₁ > = [ (at l) ] assign [ ((after l) ∧ (if x₁ then (isTrue i) else ∼ (isTrue i))) ]
transStm l < x :=b bVar x₁ > = todo
transStm l (wait x) = todo

extractLabels : List Seg → LTL
extractLabels [] = ⊥
extractLabels (se :: []) = at (label se)
extractLabels (se :: segs) = (at (label se)) ∧ (extractLabels segs)

-- Builds the relationship between statements of blocks.
blockTrans : List Seg → List TransRel
blockTrans [] = []
blockTrans (x :: []) = [] -- Add fin?
blockTrans (x :: ( y :: segs)) = [ after (label x) ] seq [ at (label y) ] :: (blockTrans ((y :: segs)))

{-# TERMINATING #-}

translate' : Seg → List TransRel
translate' (seg x stm) = (transStm x stm) :: []
translate' (block l xs) with head xs
... | Just x = ([ (at l) ] seq [ (at (label x)) ]) :: (foldl (λ ls se → (translate' se) ++ ls) [] xs ++ blockTrans xs)
... | _ = []
translate' (par x xs) = [ (at x) ] par [ extractLabels xs ] :: (conc (map (λ x → translate' x) xs))
translate' (while l (bool x) se) = bCheck :: translate' se
  where bCheck = if x then [ at l ] while [ □ (in' (label se)) ] else [ at l ] while [ ( after (label se)) ]
translate' (while l (bVar (vB i)) se) = bVarCheck :: (translate' se)
  where bVarCheck = [ at l ] while [ (at (label se) ∧ isTrue i) ∨ ((after l) ∨ (∼ (isTrue i)))]
translate' (if x x₁ se) = translate' se

translate : Prog → List TransRel
translate (prog main) = translate' main



-- after (last se) -> after l
