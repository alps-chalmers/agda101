{-
  Translator for concurrent programs. Translates program representations into
  transition relations (TransRel). The relations keep track of the LTL-formulas
  related to the program statements of the programs.
-}
module Translator where

{-***** imported modules *****-}
open import Program
open import Data.List as List
open import Label
open import LTL
open import Data.Maybe
open import Data.Nat
open import Data.Bool
{-****************************-}

{-
  Data type for actions, reference to what happened when translating the program
-}
data Action : Set where
  assign : Action  -- Assignment
  seq    : Action  -- Progress into block segment (see Program)
  par    : Action  -- Progress into a parallel segment (see Program)
  while  : Action  -- Progress into a while loop (see Program)
  or'    : Action  -- Progress into an if statement (see Program)
  inInf  : Action  -- TODO
  flowA  : Action  -- Progress between segments

{-
  Represents transition relations, < pre > action < post >, where pre is the
  precondition of the program statement, action the reference to the type of
  program statement, and post the postcondition of the statement.
-}
data TransRel : Set where
  <_>_<_> : (c₁ : LTL) → Action → (c₂ : LTL) → TransRel  -- Hoare-style Triple

{-
  Translates a program statement into the corresponding TransRel.
    * l: Program label of the program statement.
    * Stm: The program statement.
-}
transStm : Label → Stm → TransRel
transStm l < (vN x) :=n n > = < (at l) > assign < ((after l) ∧' (vN x ==n n)) >
-- (x ==n {! n  !})
transStm l < x :=b bool b > = < (at l) > assign < (after l) ∧' (if b then (isTrue x) else ∼ (isTrue x)) >
transStm l < x :=b bVar y > = < (at l) > assign < (after l) ∧' (x ==b y) >

{-
  Extracts the labels of all given segments.
-}
extractLabels : List Seg → LTL
extractLabels [] = ⊥
extractLabels (se ∷ []) = at (label se)
extractLabels (se ∷ segs) = (at (label se)) ∧' extractLabels segs

{-
  Returns the first element of the list, if there is one.
-}
head : {A : Set} → List A → Maybe A
head [] = nothing
head (x ∷ xs) = just x

{-
  Flattens a list of lists into a single list.
-}
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

{-# TERMINATING #-} -- used to guarantee that there is no infinite looping

{-
  Given a segment, returns a list of TransRel depending on the type of segment.
-}
transFlow : Seg → List TransRel
transFlow (seg _ _) = []
  -- If passed a simple segment (see Program), return empty
transFlow (block se segs) = seqFlow se segs ++ foldl (λ rels se → rels ++ transFlow se) [] segs
  -- If passed a block segment (see Program), return translation of the block
transFlow (par se segs) = < parFlow segs > flowA < after se > ∷ foldl (λ rels se → rels ++ transFlow se) [] segs
  -- If passed a parallel segment (see Program), return translation of the par
transFlow (while l _ se) = < (after (label se)) > flowA < (at l) > ∷ transFlow se
  -- If passed a while segment (see Program), return translation of the while
transFlow (if l b se) = < (after (label se)) > flowA < (after l) > ∷ (transFlow se)
  -- If passed an if segment (see Program), return translation of the if

{-# TERMINATING #-} -- used to guarantee that there is no infinite looping

{-
  Helper function for traslate that uses different tranlation approaches
  depending on the type of segment to be translated.
-}
translate' : Seg → List TransRel
translate' (seg x stm) = (transStm x stm) ∷ []
  -- If passed a normal segment, pass on to transStm and return result
translate' (block l xs) with head xs
... | just x = (< (at l) > seq < (at (label x)) > ∷ (foldl (λ ls se → (translate' se) ++ ls) [] xs))
  -- If passed a block segment with the first element being a segment, return
  -- the translation of the segment and translate all other segments
... | _ = []
  -- Else return empty
translate' (par x xs) = < (at x) > par < (extractLabels xs) > ∷ flatten (List.map (λ x → translate' x) xs)
  -- If passed a parallel segment, flatten the map with translate'
translate' (while l (bool x) se) = bCheck ∷ (translate' se)
  where bCheck = if x then < (at l) > while < (□ (in' (label se))) > else < (at l) > while < (after (label se)) >
  -- Check the boolean expression (see Program) of the while loop (see Program)
  -- and translate accordingly
translate' (while l (bVar (vB x)) se) = bVarCheck ∷ translate' se
  where bVarCheck = < at l > while < ((at (label se) ∧' isTrue (vB x)) ∨' ((after l) ∧' (∼ (isTrue (vB x))))) >
  -- As above, but with a boolean variable
translate' (if x exp se) = translate' se
  -- Translate the if statement

{-
  Translate function that takes a program and returns a list of TransRel.
  The list consists of two parts, first the statement specific translations,
  the second the program flow relations between the segments.
-}
translate : Prog → List TransRel
translate (prog main) = translate' main ++ (transFlow main) -- Pass on to
                                                            -- translate'
