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

typeof : {A : Set} -> A -> Set
typeof {A} _ = A

prog6 = program

after-b-and-p = (after Labels.b) ∧ (¬ (var Vars.p))

init = (at Labels.b) ∧ (at Labels.c)
init-id = identity init

b+p = asr-f prog6 Labels.b Vars.p
b+p-id = identity (extract-ltl b+p)

unsquig = TL12 b+p-id

after-b = d-mp (⊤-i prog6 (nd unsquig)) b+p

after-b-and-p-inv = ▢ (after-b-and-p ⊃ (▢ after-b-and-p))
after-b-and-p-event = ◇ after-b-and-p
bp-e1 = ∧-e1 (identity (after-b-and-p-inv ∧ after-b-and-p-event))
bp-e2 = ∧-e2 (identity (after-b-and-p-inv ∧ after-b-and-p-event))

eventually-always-after-b-and-p = ◇-mp bp-e1 bp-e2
prog-always-after-b-and-p = ⊤-i prog6 (nd eventually-always-after-b-and-p)

-- proof that after-b-an-p-inv satisfies at b ⊃ after-b-and-p-inv
proof2 = ∨-i2 (identity after-b-and-p-inv) (¬ (at Labels.b))
proof2' = make-implication after-b-and-p-inv (at Labels.b) --imp-eq2 proof2
proof2-imp = nd proof2'
proof2prog = ⊤-i prog6 proof2-imp
inv-assumption = ▢-i prog6 after-b-and-p
inv-implication = d-mp proof2prog inv-assumption

apply-proof : {prog : Program} {p q : Props} -> prog ⊨ p ->
                                                p ⊢ q ->
                                                ------------
                                                prog ⊨ q

apply-proof {prog} {p} {q} sat proof = d-mp (⊤-i prog (nd proof)) sat

two-imps = identity ((extract-ltl inv-implication) ∧ (extract-ltl after-b))
imp-combined = ⊃-comb (∧-e1 two-imps) (∧-e2 two-imps)

prog-imp-combined = ⊤-i prog6 (nd imp-combined)
prog-prem-comb = d-∧-i inv-implication after-b
prog-at-after-always = d-mp prog-imp-combined prog-prem-comb

chain-premise = identity ((extract-ltl prog-at-after-always)
                          ∧ (extract-ltl prog-always-after-b-and-p))


chained = hs (∧-e1 chain-premise) (∧-e2 chain-premise)

prog-both-imps = d-∧-i prog-at-after-always prog-always-after-b-and-p
chained-prog = ⊤-i prog6 (nd chained)
proved-prog = d-mp chained-prog prog-both-imps
proved-prog' = apply-proof prog-both-imps chained



always-inside-or-after-c = assume prog6 (▢ (inside Labels.c ∨ after Labels.c))

-- some things from the program
at-d-after-d = aar prog6 Labels.d -- atomic assignment rule for d
after-d-is-at-c = after-while prog6 Labels.d Labels.c -- definition, after d = at c
inside-c-at-d-or-c = inside-while prog6 Labels.c (at Labels.c ∨ at Labels.d)

-- at d ~> at c

at-after-while = ▢ ((after Labels.d) ⊃ (at Labels.c))

funny-premise = identity ((◇ (after Labels.d)) ∧
                           at-after-while)

diamond-d = ∧-e1 funny-premise
always-impy = ∧-e2 funny-premise
after-d-at-c = ◇-mp always-impy diamond-d

at-after-while-impd = make-implication at-after-while (at Labels.d)

