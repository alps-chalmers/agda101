module SafetyVerifier where

{-***** imported modules *****-}
open import Data.Bool
open import ValidProof
open import Data.List as List
open import Data.Nat
open import Program
open import LTL
open import Translator
open import Label
open import Rules
open import Function
open import Data.String as String renaming (_++_ to _s++_)
open import LTLRule
open import Truths
{-****************************-}

{-
  Equality function for ℕ - used for convinience
-}
_eq_ : ℕ → ℕ → Bool
zero eq zero = true
zero eq suc y = false
suc x eq zero = false
suc x eq suc y = x eq y

{-
  ">"-function for ℕ - for convinience
-}
_isLarger_ : ℕ → ℕ → Bool
zero isLarger zero = false
zero isLarger suc y = false
suc x isLarger zero = true
suc x isLarger suc y = x isLarger y

{-
  Checks if a given Label is in a given List of Segments
-}
_isIn'_ : Label → List Seg → Bool
s x isIn' [] = false
  -- Base case. If the function reaches the end of the List, return false
s x isIn' (seg (s x₁) x₂ ∷ segs) = if (x eq x₁) then true else ((s x) isIn' segs)
  -- If the Segment has the given Label, return true. Else keep looking
s x isIn' (block (s x₁) x₂ ∷ segs) = if (x eq x₁) then true else (if ((s x) isIn' x₂) then true else ((s x) isIn' segs))
  -- Same as the previous case
s x isIn' (par (s x₁) x₂ ∷ segs) = if (x eq x₁) then true else (if ((s x) isIn' x₂) then true else ((s x) isIn' segs))
  -- Same as the previous case
s x isIn' (while (s x₁) x₂ x₃ ∷ segs) = if (x eq x₁) then true else (if ((s x) isIn' (x₃ ∷ [])) then true else ((s x) isIn' segs))
  -- Same as the previous case
s x isIn' (if (s x₁) x₂ x₃ ∷ segs) = if (x eq x₁) then true else (if ((s x) isIn' (x₃ ∷ [])) then true else ((s x) isIn' segs))
  -- Same as the previous case

{-
  Checks if a given Label is in a Parallel Segment, calls isIn' if it reaches a
  Parallel Segment, else continues to search
-}
inPar : Label → List Seg → Bool
inPar _ [] = false
inPar (s x) (seg (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else inPar (s x) segs
inPar (s x) (block (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else (if (inPar (s x) x₂) then true else (inPar (s x) segs))
inPar (s x) (par (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else (if s x isIn' x₂ then true else (inPar (s x) segs))
  -- If the Segment is "par", check its list
inPar (s x) (while (s x₁) x₂ sg ∷ segs) = if (x eq x₁) then false else (if (inPar (s x) (sg ∷ [])) then true else (inPar (s x) segs))
inPar (s x) (if (s x₁) x₂ sg ∷ segs) = if (x eq x₁) then false else (if (inPar (s x) (sg ∷ [])) then true else (inPar (s x) segs))

{-
  Returns the Label of the Parallel Segment the given Label is in. Works like
  "inPar" above
-}
inParLabel : Label → List Seg → Label
inParLabel (s x) [] = s 0
inParLabel (s x) (seg x₁ x₂ ∷ segs) = inParLabel (s x) segs
inParLabel (s x) (block x₁ x₂ ∷ segs) = if ((s x) isIn' x₂) then (inParLabel (s x) x₂) else (inParLabel (s x) segs)
inParLabel (s x) (par x₁ x₂ ∷ segs) = if ((s x) isIn' x₂) then x₁ else (inParLabel (s x) segs)
inParLabel (s x) (while x₁ x₂ x₃ ∷ segs) = if ((s x) isIn' (x₃ ∷ [])) then (inParLabel (s x) (x₃ ∷ [])) else (inParLabel (s x) segs)
inParLabel (s x) (if x₁ x₂ x₃ ∷ segs) = if ((s x) isIn' (x₃ ∷ [])) then (inParLabel (s x) (x₃ ∷ [])) else (inParLabel (s x) segs)

{-
  Works like "inPar", except it's for While Segments instead
-}
inWhile : Label → List Seg → Bool
inWhile _ [] = false
inWhile (s x) (seg (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else inWhile (s x) segs
inWhile (s x) (block (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else (if (inWhile (s x) x₂) then true else (inWhile (s x) segs))
inWhile (s x) (par (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else (if (inWhile (s x) x₂) then true else (inWhile (s x) segs))
inWhile (s x) (while (s x₁) x₂ sg ∷ segs) = if (x eq x₁) then false else (if ((s x) isIn' (sg ∷ [])) then true else (inWhile (s x) segs))
inWhile (s x) (if (s x₁) x₂ sg ∷ segs) = if (x eq x₁) then false else (if (inWhile (s x) (sg ∷ [])) then true else (inWhile (s x) segs))

{-
  Works like "inParLabel", except it's for While Segments instead
-}
inWhileLabel : Label → List Seg → Label
inWhileLabel (s x) [] = s 0
inWhileLabel (s x) (seg x₁ x₂ ∷ segs) = inWhileLabel (s x) segs
inWhileLabel (s x) (block x₁ x₂ ∷ segs) = if ((s x) isIn' x₂) then (inWhileLabel (s x) x₂) else (inWhileLabel (s x) segs)
inWhileLabel (s x) (par x₁ x₂ ∷ segs) = if ((s x) isIn' x₂) then (inWhileLabel (s x) x₂) else (inWhileLabel (s x) segs)
inWhileLabel (s x) (while x₁ x₂ x₃ ∷ segs) = if ((s x) isIn' (x₃ ∷ [])) then x₁ else (inWhileLabel (s x) segs)
inWhileLabel (s x) (if x₁ x₂ x₃ ∷ segs) = if ((s x) isIn' (x₃ ∷ [])) then (inWhileLabel (s x) (x₃ ∷ [])) else (inWhileLabel (s x) segs)

{-
  Checks if the given Transition Relation (see Translator) breaks the given LTL
  formula by checking for contradiction
-}
_breaks_ : TransRel → LTL → Bool
< pre > assign < (after (s x)) ∧' (isTrue (vB x₁)) > breaks (∼ (isTrue (vB x₂))) = x₁ == x₂
< pre > assign < (after (s x)) ∧' (isTrue (vB x₁)) > breaks ((vB x₂) ==b (vB x₃)) = x₁ == x₂
< pre > assign < (after (s x)) ∧' ((vN x₁) ==n n₁) > breaks ((vN x₂) ==n n₂) = (x₁ == x₂) ∧ not (n₁ eq n₂)
< pre > assign < (after (s x)) ∧' (∼ (isTrue (vB x₁))) > breaks (isTrue (vB x₂)) = x₁ == x₂
< pre > assign < (after (s x)) ∧' (∼ (isTrue (vB x₁))) > breaks ((vB x₂) ==b (vB x₃)) = x₁ == x₂
< pre > assign < (after (s x)) ∧' ((vB x₁) ==b (vB x₂)) > breaks ((vB x₃) ==b (vB x₄)) = (x₁ == x₃) ∧ not (x₂ == x₄)
< pre > assign < post > breaks _  = false
< pre > _ < post > breaks _  = false

{-
  Checks if the given Transition Relation (see Translator) is located after the
  given Label by comparing the numbers of the Precondition and the Label
-}
isAfter : TransRel → Label → Bool
isAfter < at (s x) > assign < post > (s x₁) = x isLarger x₁
isAfter _ _ = false

{-
  Checks from a given Label if there exists a place in the Translation which 
  contradicts the given LTL formula 
-}
checkFrom : Label → LTL → List TransRel → Bool
checkFrom (s x) _ [] = true
  -- Base case, works since it's only being called by "_=>_,_"
checkFrom (s x) (∼ (isTrue (vB x₁))) (x₂ ∷ rels) = if (x₂ breaks (∼ (isTrue (vB x₁)))) ∧ (isAfter x₂ (s x)) then false else checkFrom (s x) (∼ (isTrue (vB x₁))) rels
  -- Checks for LTL formulae of the form "variable = false"
checkFrom (s x) (x₁ ==n n) (x₂ ∷ rels) = if (x₂ breaks (x₁ ==n n)) ∧ (isAfter x₂ (s x)) then false else checkFrom (s x) (x₁ ==n n) rels
  -- Checks for LTL formulae of the form "variable = ℕ"
--checkFrom (s x) (x₁ ==b y) rels = {!!}
checkFrom (s x) (isTrue (vB x₁)) (x₂ ∷ rels) = if ((x₂ breaks isTrue (vB x₁)) ∧ isAfter x₂ (s x)) then false else checkFrom (s x) (isTrue (vB x₁)) rels
  -- Checks for LTL formulae of the form "variable = true"
checkFrom _ _ _ = false
  -- Catch-all case

inSameWhile : Label → Label → Prog → Bool
inSameWhile l₁ l₂ (prog main) = if ((inWhile l₁ (main ∷ [])) ∧ (inWhile l₂ (main ∷ []))) then labelNum (inWhileLabel l₁ (main ∷ [])) eq labelNum (inWhileLabel l₂ (main ∷ [])) else false

inSamePar : Label → Label → Prog → Bool
inSamePar l₁ l₂ (prog main) = if ((inPar l₁ (main ∷ [])) ∧ (inPar l₂ (main ∷ []))) then ((labelNum (inParLabel l₁ (main ∷ []))) eq (labelNum (inWhileLabel l₂ (main ∷ [])))) else false

{-# TERMINATING #-}

inSameThread : Label → Label → List Seg → Bool
inSameThread l₁ l₂ [] = false
inSameThread l₁ l₂ (sg ∷ sgs) =
  if ((l₁ isIn' (sg ∷ [])) ∧ (l₂ isIn' (sg ∷ [])))
    then (if (inPar l₁ (sg ∷ []))
      then (if (inSamePar l₁ l₂ (prog (block (s 0) (sg ∷ []))))
        then (inSameThread l₁ l₂ (sg ∷ []))
      else false)
    else (if (inPar l₂ (sg ∷ []))
      then false
    else true))
  else (inSameThread l₁ l₂ sgs)

{-
  LTL₁ (of the form "after l") => LTL₂ (of the form □ LTL', where LTL' is of the
  form "variable = true/false/ℕ") , Program. Basically checks if LTL₂ will hold
  given LTL₁ and the Program associated with them. Works in different ways if
  LTL₁ is located in a Parallel Segment, in a While Segment, in both or in
  neither
-}
_=>_,_ : LTL → LTL → Prog → Bool
after l => □ (∼ (isTrue (vB x))) , prog main =
  if (inPar l (main ∷ []))
    then (if (inWhile l (main ∷ []))
      then (checkFrom (inParLabel l (main ∷ [])) (∼ (isTrue (vB x))) (translate (prog main))) ∧ (checkFrom (inWhileLabel l (main ∷ [])) (∼ (isTrue (vB x))) (translate (prog main)))
    else checkFrom (inParLabel l (main ∷ [])) (∼ (isTrue (vB x))) (translate (prog main)))
  else (if (inWhile l (main ∷ []))
    then (checkFrom (inWhileLabel l (main ∷ [])) (∼ (isTrue (vB x))) (translate (prog main)))
  else (checkFrom l (∼ (isTrue (vB x))) (translate (prog main))))
  -- Checks for LTL' (see description above) of the form "variable = false" for
  -- the different cases, calls the functions "inPar", "inParLabel", "inWhile",
  -- "inWhileLabel" and "checkFrom" as well as "translate" located in Translator
after l => □ (x ==n n) , prog main =
  if (inPar l (main ∷ []))
    then (if (inWhile l (main ∷ []))
      then (checkFrom (inParLabel l (main ∷ [])) (x ==n n) (translate (prog main))) ∧ (checkFrom (inWhileLabel l (main ∷ [])) (x ==n n) (translate (prog main)))
    else checkFrom (inParLabel l (main ∷ [])) (x ==n n) (translate (prog main)))
  else (if (inWhile l (main ∷ []))
    then (checkFrom (inWhileLabel l (main ∷ [])) (x ==n n) (translate (prog main)))
  else (checkFrom l (x ==n n) (translate (prog main))))
  -- Checks for LTL' (see description above) of the form "variable = ℕ" for the
  -- different cases, calls the functions "inPar", "inParLabel", "inWhile",
  -- "inWhileLabel" and "checkFrom" as well as "translate" located in Translator
--after l => □ (x ==b y) , prg = {!!}
after l => □ (isTrue (vB x)) , prog main =
  if (inPar l (main ∷ []))
    then (if (inWhile l (main ∷ []))
      then (checkFrom (inParLabel l (main ∷ [])) (isTrue (vB x)) (translate (prog main))) ∧ (checkFrom (inWhileLabel l (main ∷ [])) (isTrue (vB x)) (translate (prog main)))
    else checkFrom (inParLabel l (main ∷ [])) (isTrue (vB x)) (translate (prog main)))
  else (if (inWhile l (main ∷ []))
    then (checkFrom (inWhileLabel l (main ∷ [])) (isTrue (vB x)) (translate (prog main)))
  else (checkFrom l (isTrue (vB x)) (translate (prog main))))
  -- Checks for LTL' (see description above) of the form "variable = true" for
  -- the different cases, calls the functions "inPar", "inParLabel", "inWhile",
  -- "inWhileLabel" and "checkFrom" as well as "translate" located in Translator
after l => □ (x ==b y) , prog main =
  if (inPar l (main ∷ []))
    then (if (inWhile l (main ∷ []))
      then ((checkFrom (inParLabel l (main ∷ [])) (x ==b y) (translate (prog main))) ∧ (checkFrom (inWhileLabel l (main ∷ [])) (x ==b y) (translate (prog main))))
    else (checkFrom (inParLabel l (main ∷ [])) (x ==b y) (translate (prog main))))
  else (if (inWhile l (main ∷ []))
    then (checkFrom (inWhileLabel l (main ∷ [])) (x ==b y) (translate (prog main)))
  else (checkFrom l (x ==b y) (translate (prog main))))
  -- Checks for LTL' (see description above) of the form "vB x = vB y" for
  -- the different cases, calls the functions "inPar", "inParLabel", "inWhile",
  -- "inWhileLabel" and "checkFrom" as well as "translate" located in Translator
after (s x) => □ (after (s x₁)) , prog main =
  if (x eq x₁)
    then if (inWhile (s x) (main ∷ []))
      then false
    else true
  else (if (x isLarger x₁)
    then (if (inSameWhile (s x) (s x₁) (prog main))
      then false
    else (if ((inPar (s x) (main ∷ [])) ∧ (inPar (s x₁) (main ∷ [])))
      then if (inSamePar (s x) (s x₁) (prog main))
        then if (inSameThread (s x) (s x₁) (main ∷ []))
          then true
        else false
      else false
    else true))
  else false)
  -- Checks for LTL' (see description above) of the form "after l" for
  -- the different cases, calls the functions "inPar", "inParLabel", "inWhile",
  -- "inWhileLabel" and "checkFrom" as well as "translate" located in Translator
after l => □ (ltl₁ ∧' ltl₂) , prg = ((after l) => (□ ltl₁) , prg) ∧ (after l) => (□ ltl₂) , prg
  -- As the above, but for "LTL₁ ∧ LTL₂"
after l => □ (ltl₁ ∨' ltl₂) , prg = ((after l) => (□ ltl₁) , prg) ∨ (after l) => (□ ltl₂) , prg
  -- As the above, but for "LTL₁ ∨ LTL₂"
_ => _ , _ = false
  -- Catch-all case
