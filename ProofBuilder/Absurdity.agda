module Absurdity where

data ⊥' : Set where

record T' : Set where
 valid : T'
 valid = record {}
