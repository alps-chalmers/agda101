module Proc where

open import Lists
open import Props

data Proc : Set where
  proc : List Props -> Proc
