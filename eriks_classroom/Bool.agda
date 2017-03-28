module Bool where

data Bool : Set where
  true  : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

_and_ : Bool -> Bool -> Bool
true and true = true
_    and _    = false

_or_ : Bool -> Bool -> Bool
false or false = false
_     or _     = true

if_then_else_ : {A : Set} -> Bool -> A -> A -> A
if true  then x else y = x
if false then x else y = y

-- proof stuff?

data False : Set where

record True : Set where

isTrue : Bool -> Set
isTrue true = True
isTrue false = False
