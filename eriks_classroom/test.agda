module test where

open import Bool
open import N
open import Program
open import LTL
open import Validator


{-
sample program, code like this:

  integer x y ;
  a: x := 1 ;
  b: y := 2

-}

prog1 = program (seg Labels.a assignment (stm Labels.b assignment))

aaaa = aaa-i {prog1} Labels.a
aaab = aaa-i {prog1} Labels.b
aaac = aaa-i {prog1} Labels.c
compab = comp-i {prog1} Labels.a Labels.b
compac = comp-i {prog1} Labels.a Labels.c

atob = ccf {prog1} {Labels.a} {Labels.b} aaaa aaab compab
atoc = ccf {prog1} {Labels.a} {Labels.c} aaaa aaac compac

