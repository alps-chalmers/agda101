module Validator where

open import N
open import Bool
open import Program
open import LTL

composition' : Seg -> Label -> Label -> Bool
composition' (stm _ _) a b = false
composition' (seg l1 _ next) a b =
  if ((l1 == a) and ((label next) == b)) then
    true
  else
    (composition' next a b)
composition' (while _ _ contents) a b = composition' contents a b
composition' (cond _ _ contents) a b = composition' contents a b
composition' (cobegin _ proc1 proc2) a b with composition' proc1 a b
... | false = composition' proc2 a b
... | true = true

composition : Program -> Label -> Label -> Bool
composition (program contents) a b = composition' contents a b

atomicassignment' : Seg -> Label -> Bool
atomicassignment' (stm l assignment) a = l == a
atomicassignment' (seg l assignment next) a with l == a
... | true = true
... | false = atomicassignment' next a
atomicassignment' (while _ _ contents) a = atomicassignment' contents a
atomicassignment' (cond _ _ contents) a = atomicassignment' contents a
atomicassignment' (cobegin _ proc1 proc2) a with atomicassignment' proc1 a
... | true = true
... | false = atomicassignment' proc2 a

atomicassignment : Program -> Label -> Bool
atomicassignment (program prog) a = atomicassignment' prog a

proof-valid : {prop : Props} -> {prog : Program} -> prog ⊢ prop -> Bool
                                          --ticked box = case has been tested
proof-valid (assume _) = true
--conjjunction rules
proof-valid (∧-i p1 p2) = (proof-valid p1) and (proof-valid p2)    --[ ]
proof-valid (∧-e1 p) = proof-valid p                               --[ ]
proof-valid (∧-e2 q) = proof-valid q                               --[ ]
--disjjunction rules
proof-valid (∨-i1 p) = proof-valid p                              -- [ ]
proof-valid (∨-i2 q) = proof-valid q                               --[ ]
proof-valid (∨-e1 p1 p2) = (proof-valid p1) and (proof-valid p2)   --[ ]
proof-valid (∨-e2 p1 p2) = (proof-valid p1) and (proof-valid p2)   --[ ]
proof-valid (ca p1 p2 p3) = (proof-valid p1) and                   --[ ]
                            ((proof-valid p2) and
                            (proof-valid p3))
proof-valid (cd p1 p2 p3) = (proof-valid p1) and                   --[ ]
                            ((proof-valid p2) and
                            (proof-valid p3))
proof-valid (⊃-i) = true                                           --[ ]
proof-valid (mp p q) = (proof-valid p) and (proof-valid q)         --[ ]
proof-valid (mt p q) = (proof-valid p) and (proof-valid q)         --[ ]
proof-valid (hs p q) = (proof-valid p) and (proof-valid q)         --[ ]
proof-valid (ccf p1 p2 p3) = ((proof-valid p1) and                 --[ ]
                             (proof-valid p2)) and
                             (proof-valid p3)
proof-valid (ccf2 p1 p2 p3) = ((proof-valid p1) and                 --[ ]
                              (proof-valid p2)) and
                              (proof-valid p3)
-- the base cases lul
proof-valid (comp-i {prog} a b) = composition prog a b             --[ ]
proof-valid (aaa-i {prog} a) = atomicassignment prog a             --[ ]
proof-valid (cobegin-i {prog} a b c) = false -- NOT ADDED YET LUL
--proof-valid _ = true


