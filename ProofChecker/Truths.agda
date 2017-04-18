{-
  Functions and data types regarding truths, i.e. what is known
-}
module Truths where

{-***** imported modules *****-}
open import Data.List as List
open import LTL
open import Data.Bool
open import Rules
open import Data.String as String renaming (_++_ to _s++_)
{-****************************-}

{-
  Data type for Truths, is a list of LTL formulae.
-}
data Truths : Set where
  truths : List LTL → Truths

{-
  Initiates a Truths given a list of LTL.
-}
initTruths : List LTL → Truths
initTruths ltls = truths ltls

{-
  Takes a Truths and returns its list with LTL formulae.
-}
listTruths : Truths → List LTL
listTruths (truths x) = x

{-
  Finds an LTL formulae and puts a □ around it.
-}
□truth : LTL → Truths → Truths
□truth ltl₁ (truths []) = truths []
□truth ltl₁ (truths (ltl₂ ∷ ltls)) = if (isEq ltl₁ ltl₂) then truths ((□ ltl₂) ∷ ltls) else truths ((ltl₂ ∷ []) ++  listTruths (□truth ltl₁ (truths ltls)))

{-
  Checks if an LTL formulae is of the form (□ _).
-}
is□ : LTL → Bool
is□ (□ _) = true
is□ _ = false

{-
  Finds an LTL formulae with a □ around it and removes the □
-}
un□truth : LTL → Truths → Truths
un□truth (□ ltl₁) (truths []) = truths []
un□truth (□ ltl₁) (truths (ltl₂ ∷ ltls)) = if (isEq (□ ltl₁) ltl₂) then truths (ltl₁ ∷ ltls) else truths ((ltl₂ ∷ []) ++ (listTruths (un□truth (□ ltl₁) (truths ltls))))
un□truth _ tr = tr

{-
  Removes the given LTL formulae from the given Truths if it is in it.
-}
rm : LTL → Truths → Truths
rm ltl₁ (truths []) = truths []
rm ltl₁ (truths (ltl₂ ∷ ltls)) = if (isEq ltl₁ ltl₂) then (truths ltls) else (truths ((ltl₂ ∷ []) ++ (listTruths (rm ltl₁ (truths ltls)))))

{-
  Removes a given List of LTL formulae from a given Truths.
-}
rm' : List LTL → Truths → Truths
rm' [] tr = tr
rm' (ltl ∷ ltls) tr = rm' ltls (rm ltl tr)

{-
  Returns if the given LTL should stay in Truths after an update
-}
shouldStay : LTL → Bool
shouldStay (at _) = true
shouldStay (in' _) = true
shouldStay (after _) = true
shouldStay (□ _) = true
shouldStay _ = false

{-
  Removes the LTL formulae from the Truths if they shouldn't stay after an update
-}
filterTruths : List LTL → List LTL
filterTruths [] = []
filterTruths (ltl ∷ ltls) = if shouldStay ltl then filterTruths ltls else ltl ∷ (filterTruths ltls)

{-
  Updates the Truth
-}
updateTruths : List LTL → List LTL → Truths → Truths
updateTruths add rem tr = truths (add ++ filterTruths (listTruths (rm' rem tr)))

{-
  Checks if the given LTL is in the given Truths
-}
isIn : LTL → Truths → Bool
isIn ltl₁ (truths []) = false
isIn ltl₁ (truths (ltl₂ ∷ ltls)) = (isEq ltl₁ ltl₂) ∨ (isIn ltl₁ (truths ltls))

{-
  To-string for Truths
-}
pTruths : Truths → String
pTruths (truths []) = ""
pTruths (truths (ltl ∷ ltls)) = (pLTL ltl) s++ (" " s++ (pTruths (truths ltls)))

{-
  Checks if two given Truths have the same LTL formulae
-}
_areIn_ : Truths → Truths → Bool
truths [] areIn truths [] = true
truths [] areIn truths (ltl ∷ ltls) = false
truths (ltl ∷ ltls) areIn truths [] = false
truths (ltl₁ ∷ ltls₁) areIn truths (ltls₂) = if (isIn ltl₁ (truths ltls₂)) then (truths ltls₁) areIn rm ltl₁ (truths ltls₂) else false
