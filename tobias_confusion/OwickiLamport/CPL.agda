module CPL where

-- Test data
data Bool : Set where
  true  : Bool
  false : Bool

data Dummy : Set where
  foo : Dummy
  bar : Dummy   
------------

data Var (A : Set) : Set where
  --unassigned : Var A -- kanske ha ett base case som inte riktigt har en typ
  [_]        : A -> Var A

data Action : Set where
  --_:=_    : {A : Set} -> Var A -> A -> Action -- Vill ha ett "basfall" som är tilldelning av värde till variabel
  cobegin : Action -> Action -> Action
  _conc_  : Action -> Action -> Action
  --while_do_od : {A : Set} -> (A -> Bool) -> Action -> Action --Vill at något booluttryck ska uppfyllas

--data _⊢_ : (state) -> (at A) -> Set... blablabla 

