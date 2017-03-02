module test where
open import List
open import Bool
open import N
open import Maybe

data Pair (A B : Set) : Set where
  _,_ : A -> B -> Pair A B


Label = N

data Vars : Set where
  vars  : List (Pair Label N) -> List (Pair Label Bool) -> Vars

data NExpr : Set where
  nvar : Label -> NExpr
  
data BoolExpr : Set where
  bvar : Label -> BoolExpr
  bconst : Bool -> BoolExpr
data Expr : Set where
  assignN : Label -> N -> N -> Expr
  assignB : Label -> N -> Bool -> Expr
  while   : Label -> Bool -> Expr -> Expr
  concat  : Expr -> Expr -> Expr
  cobegin : Label -> Expr -> Expr -> Expr

-- lul xD naming nats for use as labels in hard coded cpl programs!
x = N0
y = N1

a = N0
b = N1
c = N2
d = N3
e = N4
f = N5
g = N6
h = N7
i = N8
j = N9


lamp1 : Pair Vars Expr
lamp1 = (vars ((x , N0) :: ((y , N0) :: [])) [] ,
         (concat (assignN a x N0)
         (concat (cobegin b
                   (concat (assignN c y N0)
                           (cobegin d
                             (assignN e y N1)
                             (assignN f y N2)))
                   (while g false
                     (assignN h x N3)))
         (assignN j x N4))))

