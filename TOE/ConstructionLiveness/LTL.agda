module LTL where

open import Bool
open import N
open import Program

data Props : Set where
  -- basic propositonal constructions
  patom           : N -> Props
  ⊥ ⊤             : Props
  _⇔_             : Props -> Props -> Props
  ¬               : Props -> Props
  _∧_ _∨_ _⊃_     : Props -> Props -> Props
  -- time related
  at inside after : Statement -> Props
  box             : Props -> Props
  ◇               : Props -> Props
  _~>_            : Props -> Props -> Props
  -- evaluation
  beval           : BExpr -> Props

infixl 10 _⊃_
infixl 15 _~>_
infixl 55 _∧_
infixl 50 _∨_

-- Section [2]: Rules
data _⊢_ : Statement -> Props -> Set where        -- descriptions of the rules
                                      -- state as an axiom / premise
  assume  : (s : Statement) ->        (p : Props) ->
                                      -----------------
                                      s ⊢ p

  -- Section [2.1]: Conjunction rules
    -- Rule [2.1.1]: conjunction introduction
  ∧-i     : {s : Statement} ->
            {p q : Props} ->
                                      (s ⊢ p) ->
                                      (s ⊢ q) ->
                                      ------------
                                      (s ⊢ (p ∧ q))

    -- Rule [2.1.2]: conjunction elimination
  ∧-e1    : {s : Statement} ->
            {p q : Props} ->
                                      s ⊢ (p ∧ q) ->
                                      --------------
                                      s ⊢ p

  ∧-e2    : {s : Statement} ->
            {p q : Props} ->
                                      s ⊢ (p ∧ q) ->
                                      --------------
                                      s ⊢ q
  ∨-i1    : {s : Statement} ->
            {p q : Props} -> 
                                      s ⊢ p ->
                                      ---------------
                                      s ⊢ (p ∨ q)
  ∨-i2    : {s : Statement} ->
            {p q : Props} -> 
                                      s ⊢ q ->
                                      ---------------
                                      s ⊢ (p ∨ q)

    -- Rule [2.2.2]: disjunctive syllogismp
  ∨-e1    : {s : Statement} ->
            {p q : Props} -> 
                                      s ⊢ (p ∨ q) ->
                                      s ⊢ (¬ p) ->
                                      ---------------
                                      s ⊢ q
  ∨-e2    : {s : Statement} ->
            {p q : Props} -> 
                                      s ⊢ (p ∨ q) ->
                                      s ⊢ (¬ q) ->
                                      ---------------
                                      s ⊢ p
    -- Rule [2.2.3]: case analisys
  ca       : {s : Statement} ->
              {p q r : Props} ->
                                      s ⊢ (p ⊃ r) ->
                                      s ⊢ (q ⊃ r) -> 
                                      s ⊢ (p ∨ q) ->
                                      ---------------
                                      s ⊢ r
    -- Rule [2.2.4]: Constructive dilemma
  cd       : {s : Statement} ->
             {p q r v : Props} ->     s ⊢ (p ⊃ r) ->
                                      s ⊢ (q ⊃ v) ->
                                      s ⊢ (p ∨ q) ->
                                      ---------------
                                      s ⊢ (r ∨ v)

  -- Section [2.3]: Implication rules
    -- Rule [2.3.1]: implication introduction
  ⊃-i     : {s : Statement} ->
            {p : Props} ->            s ⊢ (p ⊃ p) -- haha wtf? 
    -- Rule [2.3.2]: modus ponens (impication elimination)
  mp      : {s : Statement} ->
            {p q : Props} ->          s ⊢ (p ⊃ q) ->
                                      s ⊢ p ->
                                      ---------
                                      s ⊢ q
    -- Rule [2.3.3]: modus tollens (conditional elimination)
  mt      : {s : Statement } ->
            {p q : Props} ->          s ⊢ (p ⊃ q) ->
                                      s ⊢ (¬ q) ->
                                      ------------
                                      s ⊢ (¬ p)

    -- Rule [2.3.4]: hypothetical syllogysm (chain rule)
  hs      : {s : Statement} ->
            {p q r : Props} ->        s ⊢ (p ⊃ q) ->
                                      s ⊢ (q ⊃ r) ->
                                      ---------------
                                      s ⊢ (p ⊃ r)
--------------------------------                                      
--Owicki Lamport Liveness Rules
--------------------------------
      -- Rule [???]: Atomic assignment axiom
  aaa-n : (x : NVar) ->
          (n : NExpr) ->                  (assignN x n) ⊢
                                          ((at (assignN x n)) ~>
                                          (after (assignN x n)))
  aaa-b : (p : BVar) ->
          (b : BExpr) ->                  (assignB p b) ⊢
                                          ((at (assignB p b)) ~>
                                          (after (assignB p b)))
    -- Rule [???]: Concatenation control flow, page 472
  concf : {s a b : Statement} ->          a ⊢ (at a ~> after a) ->
                                          b ⊢ (at b ~> after b) ->
                                         (composition a b) ⊢
                                         --((at a) ~> (after b))
                                         (at (composition a b) ~> after (composition a b))
    -- Rule [???]: Cobegin control flow
    
  cobcf : {s a b : Statement} ->
                                      a ⊢ (at a ~> after a) ->
                                      b ⊢ (at b ~> after b) ->
                                      ------------------------------
                                      cobegin a b ⊢
                                      (at (cobegin a b) ~> after (cobegin a b))
  wer : (p : BExpr)(a : Statement) ->
                                      while p a ⊢
                                      (((at (while p a)) ∧
                                      ( box (((at (while p a)) ⊃ (¬ (beval p)))))) ~>
                                      (after (while p a)))

  wcf : (p : BExpr)(a : Statement) ->
                                      while p a ⊢
                                      ((at (while p a)) ~>
                                      ((at a) ∨ (after (while p a))))
----------------------------------------------
-- TL Rules
----------------------------------------------
  lol : {s : Statement}{p q r1 r2 : Props} ->  --Lattice Owicki Lamport Rule
                                           s ⊢ (p ~> (r1 ∨ r2)) ->
                                           s ⊢ (r1 ~> q) ->
                                           s ⊢ (r2 ~> q) ->
                                           s ⊢ (p ~> q)

  lta : (s : Statement)(p : Props) ->
                                       s ⊢ (p ~> p)
  TL7 : {s : Statement}{p q r : Props} ->
                                      s ⊢ (p ~> q) ->
                                      s ⊢ (q ~> r) ->                                      
                                      s ⊢ (p ~> r) 

{-
  ◇-p     : {a b : Props}             -> Rule (◇ a)
                                      -> Rule (a ⊃ b)
                                      ---------------
                                      -> Rule (◇ b)


-}

extract-ltl : {prog : Statement} -> {p : Props} ->  (prog ⊢ p) -> Props
extract-ltl {prog} {p} _ = p

extract-stm : {prog : Statement} -> {p : Props} ->  (prog ⊢ p) -> Statement
extract-stm {prog} {p} _ = prog
