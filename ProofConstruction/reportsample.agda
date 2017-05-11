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

-- begin box 4
box-p = identity premise
box-1 = ∧-e1 (∧-e1 box-p)
box-2 = ∧-e2 (∧-e1 box-p)
box-3 = ∧-e2 box-p

box-4 : premise ⊢ termination
box-4 = TL7imp box-1 box-2 box-3

box-5 : ⊤ ⊢ (premise ⊃ termination)
box-5 = nd box-4
-- end box 4

ass-1 = aar prog Labels.a
ass-2 = aar prog Labels.b
ass-3 = at-after prog Labels.a Labels.b

ps-1 = d-∧-i ass-1 ass-2
ps-2 = d-∧-i ps-1 ass-3
trans-1 = d-⊤-i prog box-5
ps-final = d-mp trans-1 ps-2

proof-valid : Result
proof-valid = verify ps-final
