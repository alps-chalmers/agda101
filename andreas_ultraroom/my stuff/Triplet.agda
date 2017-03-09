module Triplet where

open import Bool
open import Maybe
open import Lists

{-Just the general representation of a hoare triplet-}
data GenTriplet (A : Set) B : Set where
  [_]_[_] : A -> B -> A -> GenTriplet A B

pre' : {A B : Set} -> GenTriplet A B -> A
pre' [ pre ] _ [ _ ] = pre

post' : {A B : Set} -> GenTriplet A B -> A
post' [ _ ] _ [ post ] = post

act' : {A B : Set} -> GenTriplet A B -> B
act' [ _ ] act [ _ ] = act

chain' : {A B : Set} -> GenTriplet A (List B) -> GenTriplet A (List B) -> GenTriplet A (List B)
chain' ([ pre1 ] act1 [ post1 ]) ([ pre2 ] act2 [ post2 ]) = [ pre1 ] (act1 ++ act2) [ post2 ]
------------------------------

record Hoare (A : Set) (B : Set) : Set where
  constructor [_]_[_]
  field
   pre : A
   action : B
   post : A

hChain : {A B : Set} -> Hoare A (List B) -> Hoare A (List B) -> Hoare A (List B)
hChain H1 H2 = [ (Hoare.pre H1) ] ((Hoare.action H1) ++ (Hoare.action H2)) [ (Hoare.post H2) ]

push : {A B : Set} -> Hoare (List A) (List B) -> Hoare (List A) (List B) -> Hoare (List A) (List B)
push H1 H2 = [ (Hoare.pre H1) ++ Hoare.pre H2 ] (Hoare.action H1) ++ (Hoare.action H2) [ (Hoare.post H1) ++ (Hoare.post H2) ]

--trim : {A B : Set} -> Hoare (List A) (List B) -> Hoare (List A) (List B)
--trim H = [ (Hoare.pre H) ] (Hoare.action H) [ (rmCont (Hoare.post H)) ]

------------------------------

{-hoare triplet with bools as pre- and post conditions-}
data BoolTriplet Bool (A : Set) : Set where
  [_]_[_] : Bool -> A -> Bool -> BoolTriplet Bool A

preb : {A : Set} -> BoolTriplet Bool A -> Bool
preb [ b ] _ [ _ ] = b

postb : {A : Set} -> BoolTriplet Bool A -> Bool
postb [ _ ] _ [ b ] = b

act : {A : Set} -> BoolTriplet Bool A -> A
act [ _ ] a [ _ ] = a

{-nice thing with using bools as pre and post is that you can do more specific stuff-}

valid : {A : Set} -> BoolTriplet Bool A -> Bool
valid [ b1 ] _ [ b2 ] = b1 && b2

{-right now the part with "b2 eqB b3" is fixed by adding the function to the Bool module, though it should be interpreted as that the bool-expression b2 should be identical to b3, i.e. true eqB true is not necessarily sufficient it should be something like "b1 id b2"-}
chain : {A : Set} -> BoolTriplet Bool (List A) -> BoolTriplet Bool (List A) -> Maybe (BoolTriplet Bool (List A))
chain ( [ b1 ] a1 [ b2 ] ) ( [ b3 ] a2 [ b4 ] ) = if (b2 eqB b3) then (Just ([ b1 ] (a1 ++ a2) [ b4 ])) else Nothing

{-Current idea is that the pre- and post booleans should be something like a program state that can be evaluated into a boolean, and the action can be a list of commands executed. What would have to be added is a data type for the program state, a function that can evaluate the state into a boolean as well as a data type for actions, e.g. assignments, evaluation of booleans, etc...-}
------------------------------





--data Triplet Bool (List Action)
--  [_]_[_] : Bool -> List Action -> Bool -> Triplet Bool (List Action)

