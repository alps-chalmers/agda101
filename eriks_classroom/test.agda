module test where
open import List
open import Bool
open import N
open import Maybe

data Termination : Set where
  Foo : N -> Termination
  Bar : N -> Termination


baz : Termination -> N -> Termination
baz (Foo m) n = Foo (n + m)
baz (Bar m) n = baz (Foo (m + m)) n
