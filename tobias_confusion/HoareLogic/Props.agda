module Props where

open import Bool
open import N
open import Program

data Props : Set where
  -- basic propositonal constructions
  -- patom           : N -> Props
  ⊥ ⊤             : Props
  -- _⇔_             : Props -> Props -> Props
  ¬               : Props -> Props
  _∧_ _∨_ _⊃_     : Props -> Props -> Props
  -- time related
  --at inside after : Statement -> Props
  --box diamond     : Props -> Props
  -- _~>_            : Props -> Props -> Props
  -- evaluation
  beval           : BExpr -> Props
