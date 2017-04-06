{-
  Translator for concurrent programs. Translates program representations into
  transition relations (TransRel). The relations keep track of the LTL-formulas
  related to the program statements of the programs.
-}
module Translator where

open import Program
open import Data.List as List
open import Label
open import LTL
open import Data.Maybe
open import Data.Nat
open import Data.Bool

-- Represents program actions.
data Action : Set where
  assign : Action
  seq    : Action
  par    : Action
  while  : Action
  or'    : Action
  dummy  : Action
  inInf  : Action
  □-e    : Action
  flowA  : Action
  custom : ℕ → Action

{-
  Represents transition relations, < pre > action < post >, where pre is the
  precondition of the program statement, action the reference to the type of
  program statement, and post the postcondition of the statement.
-}
data TransRel : Set where
  todo  : TransRel
  <_>_<_> : (c₁ : LTL) → Action → (c₂ : LTL) → TransRel

{-
  Translates a program statement into the corresponding TransRel.
    * l: Program label of the program statement.
    * Stm: The program statement.
-}
transStm : Label → Stm → TransRel
transStm l < x >:=n< x₁ > = todo
transStm l < (vN x) :=n nat n > = < (at l) > assign < (after l) ∧' (x EQ n) >
transStm l < x :=n nVar x₁ > = todo
transStm l < x >:=b< x₁ > = todo
transStm l < vB i :=b bool x₁ > = < (at l) > assign < ((after l) ∧' ((if x₁ then (isTrue i) else ∼ (isTrue i)))) >
transStm l < x :=b bVar x₁ > = todo
transStm l (wait x) = todo

-- Extracts the labels of all given segments.
extractLabels : List Seg → LTL
extractLabels [] = ⊥
extractLabels (se ∷ []) = at (label se)
extractLabels (se ∷ segs) = (at (label se)) ∧' extractLabels segs

-- Returns the first element of the list, if there is one.
head : {A : Set} → List A → Maybe A
head [] = nothing
head (x ∷ xs) = just x

-- Flattens a list of lists into a single list.
flatten : {A : Set} → List (List A) → List A
flatten xs = foldl (λ x xs₁ → x ++ xs₁) [] xs

{-
  Converts a list of segments and a label, representing a single block segment,
  into a list of TransRel. The result contains the representation of the program
  flow.
  * p: Label of the parent segment.
  * List Seg: List of all child segments.
-}
seqFlow : Label → List Seg → List TransRel
seqFlow p [] = []
seqFlow p (x ∷ []) = < after (label x) > flowA < after p > ∷ []
seqFlow p (x ∷ (y ∷ xs)) = < after (label x) > flowA < at (label y) > ∷ (seqFlow p (y ∷ xs))

{-
  Converts a list of segments into a single LTL. The list represents all child
  segments initiated by a parent "par" segment. The result is an LTL used as a
  precondition in order to allow the parent segment to be considered executed.
-}
parFlow : List Seg → LTL
parFlow [] = ⊥
parFlow (x ∷ []) = after (label x)
parFlow (x ∷ xs) = (after (label x)) ∧' (parFlow xs)

{-# TERMINATING #-}

-- Given a segment, returns a list of TransRel depending on the type of segment.
transFlow : Seg → List TransRel
transFlow (seg _ _) = []
transFlow (block se segs) = seqFlow se segs ++ foldl (λ rels se → rels ++ transFlow se) [] segs
transFlow (par se segs) = < parFlow segs > flowA < after se > ∷ foldl (λ rels se → rels ++ transFlow se) [] segs
transFlow (while l _ se) = < (after (label se)) > flowA < (at l) > ∷ transFlow se
transFlow (if l b se) = < (after (label se)) > flowA < (after l) > ∷ (transFlow se)

{-# TERMINATING #-}

{-
  Helper function for traslate that uses different tranlation approaches depending
  on the type of segment to be translated.
-}

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

{-
  Translate function that takes a program and returns a list of TransRel.
  The list consists of two parts, first the statement specific translations,
  the second the program flow relations between the segments.
-}
translate : Prog → List TransRel
translate (prog main) = translate' main ++ (transFlow main)
