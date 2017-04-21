module test where

open import N
open import Bool
open import Props
open import Statement
open import Label
open import LTL


module Labels where
  a = l N0
  b = l N1
  c = l N2
  d = l N3
  e = l N4
  f = l N5
  g = l N6
  h = l N7

module Vars where
  p = bvar N0
  q = bvar N1
  w = bvar N2
  x = nvar N0
  y = nvar N1
  z = nvar N2

prog6 = program

after-b-and-p = (after Labels.b) ∧ (¬ (var Vars.p))

init = (at Labels.b) ∧ (at Labels.c)
init-id = identity init

b+p = asr-f prog6 Labels.b Vars.p
b+p-id = identity (extract-ltl b+p)

unsquig = TL12 b+p-id

after-b = d-mp (⊤-i prog6 (nd unsquig)) b+p

after-b-and-p-inv = after-b-and-p ⊃ (▢ after-b-and-p)
after-b-and-p-event = ◇ after-b-and-p
bp-e1 = ∧-e1 (identity (after-b-and-p-inv ∧ after-b-and-p-event))
bp-e2 = ∧-e2 (identity (after-b-and-p-inv ∧ after-b-and-p-event))

eventually-always-after-b-and-p = ◇-mp bp-e1 bp-e2


