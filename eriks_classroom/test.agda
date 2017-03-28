module test where

open import Bool
open import N
open import Program
open import LTL


{-
sample program, code like this:

  integer x y ;
  a: x := 1 ;
  b: y := 2

-}

a = assignN (nvar N0) (constN N1)
b = assignN (nvar N1) (constN N2)
c = assignN (nvar N1) (constN N3)

prog1 = composition a b
prog2tail = composition b c
prog2 = composition a prog2tail

aaaa = aaa-n (nvar N0) (constN N1)
aaab = aaa-n (nvar N1) (constN N2)
aaac = aaa-n (nvar N1) (constN N3)


term1 = ccf {prog1} {a} {b} aaaa aaab

termtail = ccf {prog2tail} {b} {c} aaab aaac
term2 = ccf {prog2} {a} {prog2tail} aaaa termtail


{-
prog1 = program (seg Labels.a assignment (stm Labels.b assignment))

aaaa = aaa-i {prog1} Labels.a
aaab = aaa-i {prog1} Labels.b
aaac = aaa-i {prog1} Labels.c
compab = comp-i {prog1} Labels.a Labels.b
compac = comp-i {prog1} Labels.a Labels.c

atob = ccf {prog1} {Labels.a} {Labels.b} aaaa aaab compab
atoc = ccf {prog1} {Labels.a} {Labels.c} aaaa aaac compac

-}
