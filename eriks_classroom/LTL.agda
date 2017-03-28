module LTL where

open import Bool
open import N
--open import CPL
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
  ▢ ◇             : Props -> Props
  _~>_            : Props -> Props -> Props

infixl 10 _⊃_
infixl 15 _~>_
infixl 55 _∧_
infixl 50 _∨_

{-
_~>_ : Props -> Props -> Props
a ~> b = ▢ (a ⊃ (◇ b))
-}

-- Section [2]: Rules
data _⊢_ : Statement -> Props -> Set where        -- descriptions of the rules
                                      -- state as an axiom / premise
  assume  : {s : Statement} ->        (p : Props) ->
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
  {--- Section [2.1337]: Program rules
    -- Rule [2.1337.1]: Composition introduction
  comp-i : {prog : Program} ->        (a : Label) ->
                                      (b : Label) ->
                                      prog ⊢ (comp a b)
    -- Rule [2.1337.2]: Atomic assignment axiom
  aaa-i : {prog : Program} ->         (a : Label) ->
                                      prog ⊢ (at a ~> after a)
    -- Rule [2.1337.3]: Cobegin introduction
  cobegin-i : {prog : Program} ->     (a : Label) ->
                                      (b : Label) ->
                                      (c : Label) ->
                                      --------------
                                      prog ⊢ (a =cobegin b wit c)
                                      -}
  -- Section [2.2]: Disjunction rules
    -- Rule [2.2.1]: disjunction introduction
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
    -- Rule [2.2.3]: case anasys
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
{-
  -- Section [2.4]: Biconditional rules
    -- Rule [2.4.1]: Biconditional introduction
  ⇔-i     : {p q : Props}             -> Rule (p ⊃ q)
                                      -> Rule (q ⊃ p)
                                      ---------------
                                      -> Rule (p ⇔ q)
    -- Rule [2.4.2]: Biconditional eliminitiot - dump from wikipedia list of
    -- rules, some might be redundant!!!! (probably...)
  ⇔-e1    : {p q : Props}             -> Rule (p ⇔ q)
                                      -> Rule q
                                      ---------------
                                      -> Rule p
  ⇔-e2    : {p q : Props}             -> Rule (p ⇔ q)
                                      -> Rule p
                                      ---------------
                                      -> Rule q
  ⇔-e3    : {p q : Props}             -> Rule (p ⇔ q)
                                      -> Rule (¬ q)
                                      ---------------
                                      -> Rule (¬ p)
  ⇔-e4    : {p q : Props}             -> Rule (p ⇔ q)
                                      -> Rule (¬ p)
                                      ---------------
                                      -> Rule (¬ q)
  ⇔-e5    : {p q : Props}             -> Rule (p ⇔ q)
                                      -> Rule (p ∨ q)
                                      ---------------
                                      -> Rule (p ∧ q)
  ⇔-e6    : {p q : Props}             -> Rule (p ⇔ q)
                                      -> Rule ((¬ p) ∨ (¬ q))
                                      ---------------
                                      -> Rule ((¬ p) ∧ (¬ q))
-}
{-
  -- Section [2.5]: Negation rules
    -- Rule [2.5.1]: Negation introduction (reductio ad absurdum)
  ¬-i1    : {p q : Props}             -> Rule (p ⊃ q)
                                      -> Rule (p ⊃ (¬ q))
                                      -----------------
                                      -> Rule (¬ p)
  ¬-i2    : {p q : Props}             -> Rule ((¬ p) ⊃ q)
                                      -> Rule ((¬ p) ⊃ (¬ q))
                                      -----------------
                                      -> Rule p
    -- Rule [2.5.2]: Double negation elimination
  ¬¬-e    : {p : Props}               -> Rule (¬ (¬ p))
                                      -----------------
                                      -> Rule p
    -- Rule [2.5.3]: Double negation introduction
  ¬¬-i    : {p : Props}               -> Rule p
                                      -----------------
                                      -> Rule (¬ (¬ p))


  -- TBA: ltl stuff
  -- from definition, page 463
  atafter : {a b : Statement}         -> Rule (after a)
                                      -> Composition a b
                                      ------------------
                                      -> Rule (at b)
-}
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
  ccf : {s a b : Statement} ->          a ⊢ (at a ~> after a) ->
                                        b ⊢ (at b ~> after b) ->
                                        (composition a b) ⊢
                                          (at (composition a b) ~>
                                           after (composition a b) )
    -- Rule [???]: Cobegin control flow
    {-
  ccf2 : {prog : Program}
         {a b c : Label} ->           prog ⊢ (at b ~> after b) ->
                                      prog ⊢ (at c ~> after c) ->
                                      prog ⊢ (a =cobegin b wit c) ->
                                      ------------------------------
                                      prog ⊢ (at a ~> after a)
                                      -}
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
