module Proc where

open import Lists
open import Props
open import Nat
open import Bool
open import MapFold

data Stm : Set where
  := : Stm
  par : Stm
  _hold_ : Props -> Stm

record Hoare (A : Set) (B : Set) : Set where
  constructor [_]_[_]
  field pre : A
        action : B
        post : A

data Proc : Set where
  proc : List (Hoare (List Props) Stm) -> Proc

chain : {A B : Set} -> Hoare A B -> Hoare A (List B) -> Hoare A (List B)
chain xs ys = [ (Hoare.pre ys) ] (Hoare.action xs :: (Hoare.action ys)) [ (Hoare.post xs) ]

chainProc : {A B : Set} -> Proc -> Hoare (List Props) (List Stm)
chainProc (proc empty) = [ empty ] empty [ empty ]
chainProc (proc (x :: xs)) = foldl (\ hs h → chain h hs) [ (Hoare.pre x) ] ((Hoare.action x) :: empty) [ (Hoare.post x) ] xs


-- applyRule (<>x) = iff {G} pi|pj {D,<>x}
-- applyRule ([]x) = iff {G,x} pi|pj {D,[]x}
