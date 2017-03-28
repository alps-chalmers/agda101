module Program where

open import N
open import Bool

{-Label = N

module Labels where
  a = N0
  b = N1
  c = N2
  d = N3
  e = N4
  f = N5
  g = N6
  h = N7
  i = N8
  -}


data BVar : Set where
  bvar : N -> BVar

data NVar : Set where
  nvar : N -> NVar

data BExpr : Set where
  constB : Bool -> BExpr
  rvarB  : N -> BExpr

data NExpr : Set where
  constN : N -> NExpr
  rvarN  : N -> NExpr


data Statement : Set where
  assignN      : NVar -> NExpr -> Statement
  assignB      : BVar -> BExpr -> Statement
  assignment : Statement
  composition : Statement -> Statement -> Statement
  while : BExpr -> Statement -> Statement
  cobegin : Statement -> Statement -> Statement
{-
data Props : Set where
  _∧_ : Props -> Props -> Props
  at inside after : Statement -> Props
  _~>_ : Props -> Props -> Props

data _⊢_ : Statement -> Props -> Set where
  ∧-i   : {s : Statement} ->
          {p q : Props} ->              (s ⊢ p) ->
                                        (s ⊢ q) ->
                                        --------
                                        s ⊢ (p ∧ q)

  ccf : {s a b : Statement} ->          a ⊢ (at a ~> after a) ->
                                        b ⊢ (at b ~> after b) ->
                                        (composition a b) ⊢ (at a ~> after b)

  aaa-n : (x : NVar) ->
          (n : NExpr) ->                  (assignN x n) ⊢
                                          ((at (assignN x n)) ~>
                                          (after (assignN x n)))
  aaa-b : (p : BVar) ->
          (b : BExpr) ->                  (assignB p b) ⊢
                                          ((at (assignB p b)) ~>
                                          (after (assignB p b)))


a = assignN (nvar N0) (constN N1)
b = assignN (nvar N1) (constN N2)
prog1 = composition a b

aaaa = aaa-n (nvar N0) (constN N1)
aaab = aaa-n (nvar N1) (constN N2)
term1 = ccf {prog1} {a} {b} aaaa aaab
-}
