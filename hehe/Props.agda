module Props where

open import N
open import Statement
open import Label

data Props : Set where
  -- basic propositonal constructions
  patom           : N -> Props
  var             : BVar -> Props -- value of bvar N
  ⊥ ⊤             : Props
  _⇔_             : Props -> Props -> Props
  ¬               : Props -> Props
  _∧_ _∨_ _⊃_     : Props -> Props -> Props
  -- time related
  at inside after : Label -> Props
  ▢ ◇             : Props -> Props
  _~>_            : Props -> Props -> Props

