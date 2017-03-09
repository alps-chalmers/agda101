module Program where
{-program representation in Agda-}

{-imported modules-}
--open import Nat
open import Bool
open import Lists
open import Data.Nat
open import MapFold

{-variable for natural numbers-}
data NVar : Set where
  vN : (i : ℕ) -> NVar {-each nat-var represented by a natural number-}

{-variable for booleans-}
data BVar : Set where
  vB : (i : ℕ) -> BVar {-each bool-var represented by a natural number-}

{-expressions for natural numbers-}
data ExpN : Set where
  nat : ℕ -> ExpN
  nVar : NVar -> ExpN

{-expressions for booleans-}
data ExpB : Set where
  --bool : Bool -> BVar -> ExpB
  bool : Bool -> ExpB
  bVar : BVar -> ExpB

{-general expressions, kind of a 'wrapper' for for the other expressions-}
data Exp : Set where
  expN : ExpN -> Exp
  expB : ExpB -> Exp
  _<?_ _<=?_ _>?_ _>=?_ : ExpN -> ExpN -> Exp
  _==n_ : ExpN -> ExpN -> Exp
  _==b_ : ExpB -> ExpB -> Exp
{-statements, different assignment constructors for bools and nats-}
data Stm : Set where
  <_>:=n<_> : NVar -> ExpN -> Stm
  <_:=n_> : NVar -> ExpN -> Stm
  <_>:=b<_> : BVar -> ExpB -> Stm
  <_:=b_> : BVar -> ExpB -> Stm
  wait : Exp -> Stm

{-labels, to label segments of codes-}
data Label : Set where
  s : ℕ -> Label

{-different constuctors for different segments-}
data Seg : Set where
  seg : Label -> Stm -> Seg
  block : Label -> List Seg -> Seg
  par : Label -> List Seg -> Seg
  while if : Label -> ExpB -> Seg -> Seg
  --false : Seg

{-
{-record for a program-}
record Prog : Set where
  constructor prog
  field
    init : Seg
    main : Seg
-}

data Prog : Set where
  prog : Seg -> Prog


progList : Prog -> List Seg
progList (prog (block l segs)) = segs
progList _ = empty

--compLabel
_==_ : ℕ -> ℕ -> Bool
zero == zero = true
suc x == zero = false
zero == suc y = false
suc x == suc y = x == y

compLabel : Label -> Label -> Bool
compLabel (s n1) (s n2) = n1 == n2

segLabel : Seg -> Label
segLabel (seg x x₁) = x
segLabel (block x x₁) = x
segLabel (par x x₁) = x
segLabel (while x x₁ se) = x
segLabel (if x x₁ se) = x

rightSeg : Seg -> Label -> Bool
rightSeg se l = (compLabel (segLabel se) l)

findSeg : List Seg -> Label -> List Seg
--findSeg segs l = filter (λ x → rightSeg x l) segs
findSeg empty l = empty
findSeg (seg x x₁ :: segs) l = if (rightSeg (seg x x₁) l) then (seg x x₁) :: empty else findSeg segs l
findSeg (block x x₁ :: segs) l with (rightSeg (block x x₁) l)
... | true = (block x x₁) :: empty
... | false = if isEmpty (findSeg x₁ l) then findSeg segs l else findSeg x₁ l
findSeg (par x x₁ :: segs) l with (rightSeg (par x x₁) l)
... | true = ?
... | false = ?
findSeg (while x x₁ x₂ :: segs) l = {!!}
findSeg (if x x₁ x₂ :: segs) l = {!!}
