module CPL where

open import N
open import Bool

Label = N

lA = N0
lB = N1
lC = N2
lD = N3

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
  -- <_:=_>n      : NVar -> NExpr -> Statement
  -- <_:=_>b      : BVar -> BExpr -> Statement
  assignment : Statement


data Seg : Set where
  stm : Label -> Statement -> Seg
  seg : Label -> Statement -> Seg -> Seg
  while cond : Label -> BExpr -> Seg -> Seg
  cobegin : Label -> Seg -> Seg -> Seg

label : Seg -> Label
label (stm l _) = l
label (seg l _ _) = l
label (while l _ _) = l
label (cond l _ _) = l
label (cobegin l _ _) = l


data Props : Set where
  ⊥ ⊤ : Props
  patom : N -> Props
  _∧_ : Props -> Props -> Props
  comp : Label -> Label -> Props
  at inside after : Label -> Props
  _~>_ : Props -> Props -> Props


data Program : Set where
  program : Seg -> Program



data _⊢_ : Program -> Props -> Set where
  assume :                      (p : Program) ->
                                (a : Props) ->
                                --------------
                                p ⊢ a
  composition-i :               (p : Program) ->
                                (a : Label) ->
                                (b : Label) ->
                                --------------
                                p ⊢ (comp a b)
  ∧-i : {a b : Props} -> {p : Program} ->
                                p ⊢ a ->
                                p ⊢ b ->
                                --------
                                p ⊢ (a ∧ b)




proof-valid : {prop : Props} -> {prog : Program} -> prog ⊢ prop -> Bool
proof-valid (assume _ _) = true
proof-valid (composition-i prog a b) = composition prog a b
proof-valid (∧-i p1 p2)  = (proof-valid p1) and (proof-valid p2)
proof-valid _ = true




