module Logic where

open import Imports

-- What this module does in contrast to johans proof checker when checking a proof of (premises → result) is:
-- Instead of waiting for the truth field to contain the entire proposition (premises → result) as johan do.
-- I place all premises in one(I'll get to choosing in a minute) of the too containers of known truths: propositions or proven.
-- Then while the goal(=result) proposition is not amongst those containers i apply the rule steps to the proof.


--Types

data Prop : Set where
  P : Nat → Prop
  _=>_ : Prop → Prop → Prop
  _==_ : Nat → Nat → Prop
  nothing : Prop

data Rule : Set where
  ->e : Prop → Prop → Rule
  assume_ : Prop → Rule

record Proof : Set where
  constructor pr
  field
    propositions : List Prop
    proven : List (List Prop)
    steps : List Rule
    goal : Prop

deadState : Proof
deadState = pr [] [] [] nothing


--Private functions, skip this part to understand proofchecker. Known checks both proposed and proven.

_eq_ : Prop → Prop → Bool
nothing eq nothing = true
P a eq P b = a equals b
(a => b) eq (c => d) = (a eq c) and (b eq d)
(a == b) eq (c == d) = (a equals c) and (b equals d)
_ eq _ = false

proposed : List Prop → Prop → Bool
proposed [] _ = false
proposed (x , xs) p = if (x eq p) then true else (proposed xs p)

proven : List (List Prop) → Prop → Bool
proven [] p = false
proven (xs , xss) p = if (proposed xs p) then true else (proven xss p)

known : Proof → Prop → Bool
known (pr props provs _ _) t = (proven provs t) or (proposed props t)


--Functions for passing around logic in proof record.

prove : Proof → Prop → Proof
prove (pr props (t , ts) steps goal) p = pr props ((p , t) , ts) steps goal
prove (pr props [] steps goal) p = pr props ((p , []) , []) steps goal


-- Relevant functions, read downward up for intuitive topdown understanding of proof checking

applyRule : Proof → Rule → Proof
applyRule p (assume prop) = prove p prop
applyRule p (->e x (x' => y))  = if (((x eq x') and (known p x)) and (known p (x' => y))) then (prove p y) else deadState
applyRule p (->e _ _) = deadState

goalReached : Proof → Bool
goalReached p = known p (Proof.goal p)


--The checker moves propositions from program list to proven list using the rules in steps and returns whether goal was reached in the process.

check : Proof → Bool
check p = goalReached (fold (λ proof rule → applyRule proof rule) p (Proof.steps p))
