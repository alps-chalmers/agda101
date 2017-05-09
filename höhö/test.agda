module test where

open import N
open import Bool
open import Props
open import Statement
open import Label
open import LTL
open import Veryfire
import Labels



module Vars where
  p = bvar N0
  q = bvar N1
  w = bvar N2
  x = nvar N0
  y = nvar N1
  z = nvar N2

typeof : {A : Set} -> A -> Set
typeof {A} _ = A

b = (assignB Labels.b Vars.p (constB false))
c = (while Labels.c (rvarB Vars.p)
      (assignN Labels.d Vars.x (constN N5)))
c' = (while Labels.c (rvarB Vars.p)
      (assignN Labels.e Vars.x (constN N5)))
a = cobegin Labels.a c b
a' = cobegin Labels.a c' b

prog6 = program a
after-b-and-p = (after Labels.b) ∧ (¬ (var Vars.p))

init = (at Labels.b) ∧ (at Labels.c)
init-id = identity init

b+p = asr-f prog6 Labels.b Vars.p
b+p-id = identity (extract-ltl b+p)

unsquig = TL12 b+p-id

after-b = apply-proof b+p unsquig

after-b-and-p-inv = ▢ (after-b-and-p ⊃ (▢ after-b-and-p))
after-b-and-p-event = ◇ after-b-and-p
bp-e1 = ∧-e1 (identity (after-b-and-p-inv ∧ after-b-and-p-event))
bp-e2 = ∧-e2 (identity (after-b-and-p-inv ∧ after-b-and-p-event))

eventually-always-after-b-and-p = ◇-mp bp-e1 bp-e2
prog-always-after-b-and-p = d-⊤-i prog6 (nd eventually-always-after-b-and-p)

-- proof that after-b-an-p-inv satisfies at b ⊃ after-b-and-p-inv
proof2 = ∨-i2 (identity after-b-and-p-inv) (¬ (at Labels.b))
proof2' = make-implication after-b-and-p-inv (at Labels.b) --imp-eq2 proof2
proof2-imp = nd proof2'
proof2prog = d-⊤-i prog6 proof2-imp
inv-assumption = ▢-i prog6 after-b-and-p
inv-implication = d-mp proof2prog inv-assumption


two-imps = identity ((extract-ltl inv-implication) ∧ (extract-ltl after-b))
imp-combined = ⊃-comb (∧-e1 two-imps) (∧-e2 two-imps)

prog-imp-combined = d-⊤-i prog6 (nd imp-combined)
prog-prem-comb = d-∧-i inv-implication after-b
prog-at-after-always = d-mp prog-imp-combined prog-prem-comb

chain-premise = identity ((extract-ltl prog-at-after-always)
                          ∧ (extract-ltl prog-always-after-b-and-p))


chained = hs (∧-e1 chain-premise) (∧-e2 chain-premise)

prog-both-imps = d-∧-i prog-at-after-always prog-always-after-b-and-p
chained-prog = d-⊤-i prog6 (nd chained)
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

always-not-p = ▢ (¬ (var Vars.p))
wexit = ▢ ((at Labels.c ∧ always-not-p) ⊃ (◇ (after Labels.c)))
at-c = at Labels.c
some-premise = identity ((always-not-p ∧ wexit) ∧ at-c)
sp1 = ∧-e1 (∧-e1 some-premise)
sp2 = ∧-e2 (∧-e1 some-premise)
sp3 = ∧-e2 some-premise

e-wexit = ▢-e sp2
sp3-and-sp1 = ∧-i sp3 sp1
mped-out = mp e-wexit sp3-and-sp1

--- page 2

-- premises
p2-1 = ▢ (¬ (var Vars.p))
p2-2 = (inside Labels.c) ∨ (after Labels.c)
p2-3 = ▢ ((after Labels.d) ⊃ (at Labels.c))
p2-4 = (at Labels.d) ⊃ (◇ (after Labels.d))
p2-5 = ▢ (((at Labels.c) ∧ p2-1) ⊃ (◇ (after Labels.c)))
p2-6 = (inside Labels.c) ⊃ ((at Labels.c) ∨ (at Labels.d))
-- end premisesese
big = (((((p2-2 ∧ p2-3) ∧ p2-4) ∧ p2-5) ∧ p2-6) ∧ p2-1)

big-premise = identity big
r2-1 = ∧-e2 big-premise
r2-6 = ∧-e2 (∧-e1 big-premise)
r2-5 = ∧-e2 (∧-e1 (∧-e1 big-premise))
r2-4 = ∧-e2 (∧-e1 (∧-e1 (∧-e1 big-premise)))
r2-3 = ∧-e2 (∧-e1 (∧-e1 (∧-e1 (∧-e1 big-premise))))
r2-2 = ∧-e1 (∧-e1 (∧-e1 (∧-e1 (∧-e1 big-premise))))


-- box 2-1
box-2-1-p = identity (p2-3 ∧ (◇ (after Labels.d)))
box-2-1-2 = ∧-e2 box-2-1-p
box-2-1-3 = ∧-e1 box-2-1-p
box-2-1-4 = ◇-mp box-2-1-3 box-2-1-2
box-2-1-5 = weaken box-2-1-4
box-2-1-6 = nd box-2-1-5
-- end box 2-1

p2-7 = ⊤-i box-2-1-6 big
p2-8 = mp p2-7 r2-3
p2-9 = hs r2-4 p2-8


-- box 2-2
box-2-2-p = identity ((p2-5 ∧ p2-1) ∧ (at Labels.c))
box-2-2-1 = ∧-e1 (∧-e1 box-2-2-p)
box-2-2-2 = ∧-e2 (∧-e1 box-2-2-p)
box-2-2-3 = ∧-e2 box-2-2-p
box-2-2-4 = ∧-i box-2-2-3 box-2-2-2
box-2-2-5 = ▢-e box-2-2-1
box-2-2-6 = mp box-2-2-5 box-2-2-4
box-2-2-7 = weaken box-2-2-6
box-2-2-8 = nd box-2-2-7
-- end box 2-2

p2-10 = ⊤-i box-2-2-8 big
p2-11 = ∧-i r2-5 r2-1
p2-12 = mp p2-10 p2-11

p2-13 = ◇-hs p2-9 p2-12

-- box 2-3
box-2-3-p = identity (after Labels.c)
box-2-3-1 = ◇-i box-2-3-p
box-2-3-2 = nd box-2-3-1
-- end box 2-3

p2-14 = ⊤-i box-2-3-2 big


-- box-2-4
box-2-4-p = identity (((at Labels.c ⊃ (◇ (after Labels.c))) ∧
                      (at Labels.d ⊃ (◇ (after Labels.c)))) ∧ 
                      ((at Labels.c) ∨ (at Labels.d)))

box-2-4-1 = ∧-e1 (∧-e1 box-2-4-p)
box-2-4-2 = ∧-e2 (∧-e1 box-2-4-p)
box-2-4-3 = ∧-e2 box-2-4-p
box-2-4-4 = ca box-2-4-1 box-2-4-2 box-2-4-3
box-2-4-5 = weaken box-2-4-4
box-2-4-6 = nd box-2-4-5
-- end box 2-4

p2-15 = ⊤-i box-2-4-6 big
p2-16 = ∧-i p2-12 p2-13
p2-17 = mp p2-15 p2-16
p2-18 = hs r2-6 p2-17

-- box 2-5
box-2-5-p = identity (((inside Labels.c ⊃ (◇ (after Labels.c))) ∧
                      (after Labels.c ⊃ (◇ (after Labels.c)))) ∧
                      (inside Labels.c ∨ after Labels.c))
box-2-5-1 = ∧-e1 (∧-e1 box-2-5-p)
box-2-5-2 = ∧-e2 (∧-e1 box-2-5-p)
box-2-5-3 = ∧-e2 box-2-5-p
box-2-5-4 = ca box-2-5-1 box-2-5-2 box-2-5-3
box-2-5-5 = weaken box-2-5-4
box-2-5-6 = nd box-2-5-5
--- end box-2-5
p2-19 = ⊤-i box-2-5-6 big
p2-20 = ∧-i p2-18 p2-14
p2-21 = mp p2-19 p2-20
p2-22 = mp p2-21 r2-2

p2-a1 = assume prog6 (▢ ((inside Labels.c) ∨ (after Labels.c)))
p2-a2 = after-while prog6 Labels.d Labels.c
p2-a3 = aar prog6 Labels.d
p2-a4 = wer prog6 Labels.c (var (Vars.p))
p2-a5 = inside-while prog6 Labels.c ((at Labels.c) ∨ (at Labels.d))

-- box 2-6
box-2-6-p = identity (▢ ((inside Labels.c) ∨ (after Labels.c)))
box-2-6-1 = ▢-e box-2-6-p
box-2-6-2 = nd box-2-6-1
-- end box-2-6

p2-23 = d-⊤-i prog6 box-2-6-2
p2-24 = d-mp p2-23 p2-a1

-- box 2-7
box-2-7-p = identity ((at Labels.d) ~> (after Labels.d))
box-2-7-1 = TL12 box-2-7-p
box-2-7-2 = nd box-2-7-1
-- end box 2-7
p2-25 = d-⊤-i prog6 box-2-7-2
p2-26 = d-mp p2-25 p2-a3

p2-27 = weaken p2-22
p2-28 = nd p2-27

p2-29 = d-∧-i p2-24 p2-a2
p2-30 = d-∧-i p2-29 p2-26
p2-31 = d-∧-i p2-30 p2-a4
p2-32 = d-∧-i p2-31 p2-a5

p2-33 = d-⊤-i prog6 p2-28
p2-34 = d-mp p2-33 p2-32

-- box 2-8
box-2-8-p = identity (▢ after-b-and-p)
box-2-8-1 = TL4 box-2-8-p
box-2-8-2 = ∧-e2 box-2-8-1
box-2-8-3 = nd box-2-8-2
box-2-8-4 = ▢-⊤ box-2-8-3
-- end box 2-8

-- box 2-9
box-2-9-p = identity ((▢ (▢ after-b-and-p ⊃ ▢ (¬ (var Vars.p))))
                      ∧ (◇ (▢ after-b-and-p)))
box-2-9-1 = ∧-e1 box-2-9-p
box-2-9-2 = ∧-e2 box-2-9-p
box-2-9-3 = ◇-mp box-2-9-1 box-2-9-2
box-2-9-4 = weaken box-2-9-3
box-2-9-5 = nd box-2-9-4

p2-35 = d-⊤-i prog6 box-2-8-4
p2-36 = d-⊤-i prog6 box-2-9-5
p2-37 = d-mp p2-36 p2-35

-- box 2-10
box-2-10-p = identity ((at Labels.b ⊃ ◇ (▢ after-b-and-p)) ∧
                      (◇ (▢ after-b-and-p) ⊃ ◇ (▢ (¬ (var Vars.p)))))
box-2-10-1 = ∧-e1 box-2-10-p
box-2-10-2 = ∧-e2 box-2-10-p
box-2-10-3 = hs box-2-10-1 box-2-10-2
box-2-10-4 = nd box-2-10-3
-- end box 2-10

p2-38 = d-⊤-i prog6 box-2-10-4
p2-39 = d-∧-i proved-prog p2-37
p2-40 = d-mp p2-38 p2-39

-- box 2-11
box-2-11-p = identity ((at Labels.b ⊃ ◇ (▢ (¬ (var Vars.p)))) ∧
                      (p2-1 ⊃ ◇ (after Labels.c)))
box-2-11-1 = ∧-e1 box-2-11-p
box-2-11-2 = ∧-e2 box-2-11-p
box-2-11-3 = ◇-hs box-2-11-1 box-2-11-2
box-2-11-4 = nd box-2-11-3
-- end box 2-11

p2-41 = d-⊤-i prog6 box-2-11-4
p2-42 = d-∧-i p2-40 p2-34
p2-43 = d-mp p2-41 p2-42


{--

at this point p2-43 is prog6 ⊨ (at Labels.b ⊃ ◇ (after Labels.c))
    and proved-prog is prog6 ⊨ (at Labels.b ⊃ ◇ (▢  (after Labels.b ∧ (¬ p)))
    so if we change it to (at Labels.b ⊃ ◇ (▢ (after Labels.b) ∧ (after Labels.c

--}
after-c-inv = ▢ ((after Labels.c) ⊃ (▢ (after Labels.c)))

-- box 2-12
box-2-12-p = identity (after-c-inv ∧ (◇ (after Labels.c)))
box-2-12-1 = ∧-e2 box-2-12-p
box-2-12-2 = ∧-e1 box-2-12-p
box-2-12-3 = ◇-mp box-2-12-2 box-2-12-1
box-2-12-4 = weaken box-2-12-3
box-2-12-5 = nd box-2-12-4
-- end box 2-12



p2-44 = ▢-i prog6 (after Labels.c)
p2-45 = d-⊤-i prog6 box-2-12-5
p2-46 = d-mp p2-45 p2-44

-- box 2-13
box-2-13-p = identity ((at Labels.b ⊃ ◇ (after Labels.c)) ∧
                       ((◇ (after Labels.c)) ⊃ ◇ (▢  (after Labels.c))))
box-2-13-1 = ∧-e1 box-2-13-p
box-2-13-2 = ∧-e2 box-2-13-p
box-2-13-3 = hs box-2-13-1 box-2-13-2
box-2-13-4 = nd box-2-13-3
-- end box 2-13

p2-47 = d-⊤-i prog6 box-2-13-4
p2-48 = d-∧-i p2-43 p2-46
p2-49 = d-mp p2-47 p2-48

--p2-50 = d-∧-i p2-

-- box 2-14
box-2-14-p = identity (▢ after-b-and-p)
box-2-14-1 = TL4 box-2-14-p
box-2-14-2 = ∧-e1 box-2-14-1
box-2-14-3 = nd box-2-14-2
box-2-14-4 = ▢-⊤ box-2-14-3
-- end box 2-14

-- box 2-15
box-2-15-p = identity (◇ (▢ after-b-and-p))
box-2-15-1 = ⊤-i box-2-14-4 (◇ (▢ after-b-and-p))
box-2-15-2 = ◇-mp box-2-15-1 box-2-15-p
box-2-15-3 = nd box-2-15-2
-- end box 2-15

-- box-2-16
box-2-16-p' = ((at Labels.b) ⊃ (◇ (▢ after-b-and-p)))
box-2-16-p = identity box-2-16-p'
box-2-16-1 = ⊤-i box-2-15-3 box-2-16-p'
box-2-16-2 = hs box-2-16-p box-2-16-1
box-2-16-3 = nd box-2-16-2
-- end box 2-16

p2-50 = d-⊤-i prog6 box-2-16-3
p2-51 = d-mp p2-50 proved-prog
--p2-51 = d-mp

-- box 2-17
box-2-17-p = identity (((at Labels.b) ⊃ (◇ (▢ (after Labels.b)))) ∧
                      ((at Labels.b) ⊃ (◇ (▢ (after Labels.c)))))
box-2-17-1 = ∧-e1 box-2-17-p
box-2-17-2 = ∧-e2 box-2-17-p
box-2-17-3 = TL14 box-2-17-1 box-2-17-2
box-2-17-4 = nd box-2-17-3
-- end box 2-17

p2-52 = d-⊤-i prog6 box-2-17-4
p2-53 = d-∧-i p2-51 p2-49
p2-54 = d-mp p2-52 p2-53


proof-valid = verify p2-54
