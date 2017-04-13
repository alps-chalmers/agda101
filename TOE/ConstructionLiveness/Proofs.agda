module Proofs where

open import Bool
open import N
open import Program
open import LTL


typeof : {A : Set} -> A -> Set
typeof {A} _ = A


{-
Simple Terminating Concatenated program:

  int x y ;
  a: x := 1 ;
  b: y := 2

-}

--Program 
a = assignN (nvar N0) (constN N1)
b = assignN (nvar N1) (constN N2)

prog = composition a b


--Proof of individual liveness
aaaa = aaa-n (nvar N0) (constN N1)
aaab = aaa-n (nvar N1) (constN N2)

--Proof that at prog ~> after prog ≡ at a ~> after b 
term1 = concf {composition a b} {a} {b} aaaa aaab

{-
Simple Terminating Cobegin Program:

  bool x y ;
  a: cobegin 
         b: x = true 
     with
         c: y = false
     coend
-}

--Program

x = bvar N0
y = bvar N1

T = constB true
F = constB false

bb = assignB x T
bc = assignB y F

ba = cobegin bb bc

--Proof of individual liveness
baaab = aaa-b x T  --proof of at b ~> after b
baaac = aaa-b y F  -- -||-

--Proof of at a ~> after a
bterm = cobcf {ba} {bb} {bc} baaab baaac

{-
Simple Terminating While Program:

  bool x, y;
  a: x := true ;
  b: while x do   c: x = false    od

Want to show: 
     at a ~> after b
-}

wc = assignB x F
wa = assignB x T
wb = while (rvarB x) wc
ws = composition wa wb

--Proof and assumptions
wterma = aaa-b x T
wflowb = wcf (rvarB x) wc
--wtriv = lta wb (after wb) 
wtriv = assume wb ((after wb)  ~> (after wb))
wsafety = assume wb ((at wc) ~> ((at wb) ∧ (box (((at wb) ⊃ (¬ (beval (rvarB x))))))))
wexit = wer (rvarB x) wc
watc = TL7 wsafety wexit
watb = lol wflowb watc wtriv

wterm = concf {ws}{wa}{wb} wterma watb
