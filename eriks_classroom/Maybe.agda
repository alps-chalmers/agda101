module Maybe where
import Bool
open Bool

data Maybe (A : Set) : Set where
  Nothing : Maybe A
  Just : A -> Maybe A

isNothing : {A : Set} -> Maybe A -> Bool
isNothing Nothing = true
isNothing _       = false

isJust : {A : Set} -> Maybe A -> Bool
isJust x = not (isNothing x)

