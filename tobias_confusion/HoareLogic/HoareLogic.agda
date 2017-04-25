module HoareLogic where

open import Bool
open import N
open import Props
open import Program

typeof : {A : Set} -> A -> Set
typeof {A} _ = A

_N==_ : NExpr -> NExpr -> Bool
(n N* m) N== (k N* l) = (n N== m) and (k N== l)
(_ N* _) N== _ = false
(n N+ m) N== (k N+ l) = (n N== m) and (k N== l)
(_ N+ _) N== _ = false
(n N- m) N== (k N- l) = (n N== m) and (k N== l)
(_ N- _) N== _ = false
constN x N== constN y = x == y
constN _ N== _ = false
rvarN (nvar n) N== rvarN (nvar m) = n == m
rvarN _ N== _ = false
static n N== static m = n N== m --maybe always false
static n N== _ = false

replaceEqualN : NExpr -> N -> N -> NVar -> NExpr
replaceEqualN _ zero zero x = rvarN x
replaceEqualN a zero _ _ = a
replaceEqualN a _ zero _ = a
replaceEqualN a (s n) (s m) x = replaceEqualN a n m x

replaceNN : NExpr -> NExpr -> NVar -> NExpr
replaceNN (n N* m) (k N* l) x =
    if (n N== k) and (m N== l) then (rvarN x) else ((replaceNN n (k N+ l) x) N* (replaceNN m (k N* l) x))
replaceNN (n N* m) k x                         = ((replaceNN n k x) N* (replaceNN m k x))
replaceNN (n N+ m) (k N+ l) x                  =
    if (n N== k) and (m N== l) then (rvarN x) else ((replaceNN n (k N+ l) x) N+ (replaceNN m (k N+ l) x))
replaceNN (n N+ m) x y                         = (replaceNN n x y) N+ (replaceNN m x y)
replaceNN (n N- m) (k N- l) x                  =
    if (n N== k) and (m N== l) then (rvarN x) else ((replaceNN n (k N- l) x) N+ (replaceNN m (k N- l) x))
replaceNN (n N- m) x y                         = (replaceNN n x y) N- (replaceNN m x y)
replaceNN (constN n) (constN m) x              = replaceEqualN (constN n) n m x
replaceNN (constN n) _ _                       = (constN n)
replaceNN (rvarN (nvar n)) (rvarN (nvar m)) x  = replaceEqualN (rvarN (nvar n)) n m x
replaceNN (rvarN n) _ _                        = (rvarN n)
replaceNN (static n) _ _                       = static n

replaceBN : BExpr -> NExpr -> NVar -> BExpr
replaceBN (constB x) _ _  = (constB x)
replaceBN (rvarB x) _ _   = (rvarB x)
replaceBN (n N> m) x y    = (replaceNN n x y ) N> (replaceNN m x y)
replaceBN (n N< m) x y    = (replaceNN n x y ) N< (replaceNN m x y)
replaceBN (n N>= m) x y   = (replaceNN n x y ) N>= (replaceNN m x y)
replaceBN (n N<= m) x y   = (replaceNN n x y ) N<= (replaceNN m x y)
replaceBN (n N= m) x y    = (replaceNN n x y ) N= (replaceNN m x y)

replacePN : Props -> NExpr -> NVar -> Props
replacePN (beval b) n x = beval (replaceBN b n x)
replacePN ⊤ _ _ = ⊤
replacePN ⊥ _ _ = ⊥
replacePN (¬ p) n x = ¬ (replacePN p n x)
replacePN (p ∧ q) n x =  (replacePN p n x) ∧ (replacePN p n x)
replacePN (p ∨ q) n x =  (replacePN p n x) ∨ (replacePN p n x)
replacePN (p ⊃ q) n x =  (replacePN p n x) ⊃ (replacePN p n x)

data _⊢_ : Props -> Props -> Set where
  axiom : (p : Props) -> ⊤ ⊢ p
  -- Typ eriks datatyp med hur man kan manipulera LTL-statements fast
  -- fast för sekventiella grejer, orkar inte skriva in det, vanliga
  -- proplogic-regler

data _[_]_ : Props -> Statement -> Props -> Set where
  assume : (p q : Props)(s : Statement) ->
                                              p [ s ] q
  -- D0 p(e) {x:=e} p(x)
  D0-n : (p : Props)(n : NVar)(e : NExpr) -> -- för assign av Nat till Nat
                                              p [ assignN n e ] (replacePN p e n)
  -- D0-b : (p : Props)(b : BVar)(e : BExpr) ->
  --                                            p [ assignB b e ] (replacePB p e b)
  -- D1 a) p{q}r and ⊢ r⊃s then p{q}s
  -- D1 b) p{q}r and ⊢ s⊃p then s{q}r
  D1-a : {p r s t : Props}{q : Statement} ->  t ⊢ (r ⊃ s) ->
                                              p [ q ] r ->
                                              --------------
                                              p [ q ] s
  D1-b : {p r s t : Props}{q : Statement} ->  t ⊢ (s ⊃ p) ->
                                              p [ q ] r ->
                                              --------------
                                              p [ q ] r
-- D2 p{q1}r1, r1{q2}r then p{q1;q2}r
  D2   : {p r1 r : Props}{q1 q2 : Statement} ->
                                              p [ q1 ] r1 ->
                                              r1 [ q2 ] r ->
                                             --------------
                                              p [ composition q1 q2 ] r
-- D3 p, b{s}p then p{while b do s} (¬b ∧ p)
  D3   : {p : Props}{b : BExpr}{s : Statement} ->
                                              (beval b) [ s ] p ->
                                              --------------------
                                              p [ while b s ] ((¬ (beval b)) ∧ p)
