module Translator where

open import Program
open import Data.List as List
open import Label
open import LTL
open import Data.Maybe
open import Data.Nat
open import Data.Bool

data Action : Set where
  assign : Action
  par    : Action
  seq    : Action
  while  : Action
  or'    : Action
  dummy  : Action
  inInf  : Action
  □-e    : Action
  flowA  : Action
  custom : ℕ → Action

data TransRel : Set where
  todo  : TransRel
  <_>_<_> : (c₁ : LTL) → Action → (c₂ : LTL) → TransRel

transStm : Label → Stm → TransRel
transStm l < x >:=n< x₁ > = todo
transStm l < (vN x) :=n nat n > = < (at l) > assign < (after l) ∧' (x EQ n) >
transStm l < x :=n nVar x₁ > = todo
transStm l < x >:=b< x₁ > = todo
transStm l < vB i :=b bool x₁ > = < (at l) > assign < ((after l) ∧' ((if x₁ then (isTrue i) else ∼ (isTrue i)))) >
transStm l < x :=b bVar x₁ > = todo
transStm l (wait x) = todo

extractLabels : List Seg → LTL
extractLabels [] = ⊥
extractLabels (se ∷ []) = at (label se)
extractLabels (se ∷ segs) = (at (label se)) ∧' extractLabels segs

head : {A : Set} → List A → Maybe A
head [] = nothing
head (x ∷ xs) = just x

flatten : {A : Set} → List (List A) → List A
flatten xs = foldl (λ x xs₁ → x ++ xs₁) [] xs

seqFlow : Label → List Seg → List TransRel
seqFlow p [] = []
seqFlow p (x ∷ []) = < after (label x) > flowA < after p > ∷ []
seqFlow p (x ∷ (y ∷ xs)) = < after (label x) > flowA < at (label y) > ∷ (seqFlow p (y ∷ xs))

parFlow : List Seg → LTL
parFlow [] = ⊥
parFlow (x ∷ []) = after (label x)
parFlow (x ∷ xs) = (after (label x)) ∧' (parFlow xs)

{-# TERMINATING #-}

transFlow : Seg → List TransRel
transFlow (seg _ _) = []
transFlow (block se segs) = seqFlow se segs ++ foldl (λ rels se → rels ++ transFlow se) [] segs
transFlow (par se segs) = < parFlow segs > flowA < after se > ∷ foldl (λ rels se → rels ++ transFlow se) [] segs
transFlow (while l _ se) = < (after (label se)) > flowA < (at l) > ∷ transFlow se
transFlow (if l b se) = < (after (label se)) > flowA < (after l) > ∷ (transFlow se)

{-# TERMINATING #-}

translate' : Seg → List TransRel
translate' (seg x stm) = (transStm x stm) ∷ []
translate' (block l xs) with head xs
... | just x = (< (at l) > seq < (at (label x)) > ∷ (foldl (λ ls se → (translate' se) ++ ls) [] xs))
... | _ = []
translate' (par x xs) = < (at x) > par < (extractLabels xs) > ∷ flatten (List.map (λ x → translate' x) xs)
translate' (while l (bool x) se) = bCheck ∷ (translate' se)
  where bCheck = if x then < (at l) > while < (□ (in' (label se))) > else < (at l) > while < (after (label se)) >
translate' (while l (bVar (vB i)) se) = bVarCheck ∷ translate' se
  where bVarCheck = < at l > while < ((at (label se) ∧' isTrue i) ∨' ((after l) ∧' (∼ (isTrue i)))) >
translate' (if x exp se) = translate' se

translate : Prog → List TransRel
translate (prog main) = translate' main ++ (transFlow main)
