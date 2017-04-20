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

-- atomic assignemnt rule applied t B
asr-b = asr-f {prog6} {Labels.b} {Vars.p}

-- initial assumption
init = assume {prog6} ((at Labels.b) ∧ (at Labels.c))
atb = mp (∧-e1 {prog6} (at Labels.b) (at Labels.c)) init

unsquiggled-p = TL12 asr-b
ab+p-false = mp unsquiggled-p atb
ab+p-false-invariant = ▢-i {prog6} {((after Labels.b) ∧ (¬ (var Vars.p)))}

ab+p-false-eventually-always = ◇-mp ab+p-false ab+p-false-invariant

ab-and-p-false-always = TL4a1 {prog6} (after Labels.b) (¬ (var Vars.p))

ab-p-elim = ∧-e2 {prog6} (▢ (after Labels.b)) (▢ (¬ (var Vars.p)))

ab-p-false-always = ◇-mp ab+p-false-eventually-always ab-and-p-false-always

p-false-always = ◇-mp ab-p-false-always ab-p-elim

-- hehe
c-status-always = assume {prog6} (▢ ((inside Labels.c) ∨ (after Labels.c)))
c-status = ▢-e c-status-always

c-status-and-p-eventually = ∧-i p-false-always c-status-always

c-status-and-p-false-always = TL11 c-status-and-p-eventually

always-p-disted = ∧-dist {prog6} (▢ (¬ (var Vars.p))) (inside Labels.c) (after Labels.c)

c-status-p-dist = ◇-mp c-status-and-p-false-always always-p-disted




