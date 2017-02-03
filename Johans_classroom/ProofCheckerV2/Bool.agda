module Bool where

data Bool : Set where
  true : Bool
  false : Bool

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true then t else f = t
if false then t else f = f

_&&_ : Bool -> Bool -> Bool
true && true = true
_ && _ = false

_||_ : Bool -> Bool -> Bool
false || false = false
_ || _ = true
