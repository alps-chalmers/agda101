module State where

open import Lists
open import Nat
open import Bool
open import MapFold

data Formula : Set where
  F : Formula
  P : Nat -> Formula
  _=>_ : Formula -> Formula -> Formula
  _eqN_ : Nat -> Nat -> Formula -- Variable number

data Rule : Set where
  ->e : Formula -> Formula -> Rule
  ->i : Rule
  assume_ : Formula -> Rule

record State : Set where
  constructor st
  field
    init : List Formula
    truths : List (List Formula)
    proof : List Rule
    goal : Formula

_eqF_ : Formula -> Formula -> Bool
F eqF F = true
(P x) eqF (P y) = x == y
(p1 => q1) eqF (p2 => q2) = (p1 eqF p2) && (q1 eqF q2)
(x1 eqN n1) eqF (x2 eqN n2) = (x1 == x2) && (n1 == n2)
_ eqF _ = false

topLayer : State -> List Formula
topLayer (st _ empty _ _ ) = empty
topLayer (st init (t :: ts) proof goal) = t

popLayer : State -> State
popLayer (st init empty proof goal) = st init empty proof goal
popLayer (st init (t :: ts) proof goal) = st init ts proof goal

goalReached' : List Formula -> Formula -> Bool
goalReached' empty g = false
goalReached' (x :: xs) g = if (x eqF g) then true else (goalReached' xs g)

goalReached : State -> Bool
goalReached s = foldl (λ b f' → b || ((State.goal s) eqF f')) false (topLayer s)

isTrue : State -> Formula -> Bool
isTrue s f = foldl (λ b f' → b || (f eqF f')) false (conc (State.truths s)) || foldl (λ b f' → b || (f eqF f')) false (State.init s)

addTruth : State -> Formula -> State
addTruth (st init (t :: ts) proof goal) f = st init ((f :: t) :: ts) proof goal
addTruth (st init empty proof goal) f = st init ((f :: empty) :: empty) proof goal
