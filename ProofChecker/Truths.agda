module Truths where

open import Data.List
open import LTL
open import Data.Bool
open import Rules

data Truths : Set where
  truths : List LTL → Truths

innitTruths : List LTL → Truths
innitTruths ltls = truths ltls

listTruths : Truths → List LTL
listTruths (truths x) = x

□truth : LTL → Truths → Truths
□truth ltl₁ (truths []) = truths []
□truth ltl₁ (truths (ltl₂ ∷ ltls)) = if (isEq ltl₁ ltl₂) then truths ((□ ltl₂) ∷ ltls) else truths ((ltl₂ ∷ []) ++  listTruths (□truth ltl₁ (truths ltls)))

is□ : LTL → Bool
is□ (□ _) = true
is□ _ = false

un□truth : LTL → Truths → Truths
un□truth (□ ltl₁) (truths []) = truths []
un□truth (□ ltl₁) (truths (ltl₂ ∷ ltls)) = if (isEq (□ ltl₁) ltl₂) then truths (ltl₁ ∷ ltls) else truths ((ltl₂ ∷ []) ++ (listTruths (un□truth (□ ltl₁) (truths ltls))))
un□truth _ tr = tr

rm : LTL → Truths → Truths
rm ltl₁ (truths []) = truths []
rm ltl₁ (truths (ltl₂ ∷ ltls)) = if (isEq ltl₁ ltl₂) then (truths ltls) else (truths ((ltl₂ ∷ []) ++ (listTruths (rm ltl₁ (truths ltls)))))

rm' : List LTL → Truths → Truths
rm' [] tr = tr
rm' (ltl ∷ ltls) tr = rm' ltls (rm ltl tr)

shouldStay : LTL → Bool
shouldStay (at _) = true
shouldStay (in' _) = true
shouldStay (after _) = true
shouldStay (□ _) = true
shouldStay _ = false

filterTruths : List LTL → List LTL
filterTruths [] = []
filterTruths (ltl ∷ ltls) = if shouldStay ltl then filterTruths ltls else ltl ∷ (filterTruths ltls)

updateTruths : List LTL → List LTL → Truths → Truths
updateTruths add rem tr = truths (add ++ filterTruths (listTruths (rm' rem tr)))
