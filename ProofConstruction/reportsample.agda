module reportsample where

open import Statement
open import LTL
open import Label
open import Props
open import N
open import Veryfire
import Labels
import Vars

a = assignN Labels.a Vars.x (constN N5)
b = assignN Labels.b Vars.y (constN N6)

prog = program (composition a b)

termination = (at Labels.a) ~> (after Labels.b)
a-term = (at Labels.a) ~> (after Labels.a)
b-term = (at Labels.b) ~> (after Labels.b)
after-a-b = ▢ ((after Labels.a) ⊃ (at Labels.b))
premise = (((a-term) ∧ (b-term)) ∧ after-a-b)

-- begin box
box-p = identity premise
box-1 = ∧-e1 (∧-e1 box-p)
box-2 = ∧-e2 (∧-e1 box-p)
box-3 = ∧-e2 box-p

box-4 : premise ⊢ termination
box-4 = TL7imp box-1 box-2 box-3

box-5 : ⊤ ⊢ (premise ⊃ termination)
box-5 = nd box-4
-- end box

assumption-1 = aar prog Labels.a
assumption-2 = aar prog Labels.b
assumption-3 = at-after prog Labels.a Labels.b

proofstep-1 = d-∧-i assumption-1 assumption-2
proofstep-2 = d-∧-i proofstep-1 assumption-3
transition-1 = d-⊤-i prog box-5
proofstep-final = d-mp transition-1 proofstep-2

proof-valid : Result
proof-valid = verify proofstep-final
