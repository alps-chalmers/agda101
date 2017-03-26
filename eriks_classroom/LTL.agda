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
  at inside after : Label -> Props
  ▢ ◇             : Props -> Props
  _~>_            : Props -> Props -> Props
  -- program related
  comp            : Label -> Label -> Props
  _=cobegin_wit_ : Label -> Label -> Label -> Props

infixl 10 _⊃_
infixl 15 _~>_
infixl 55 _∧_
infixl 50 _∨_

{-
_~>_ : Props -> Props -> Props
a ~> b = ▢ (a ⊃ (◇ b))
-}

-- Section [2]: Rules
data _⊢_ : Program -> Props -> Set where        -- descriptions of the rules
                                      -- state as an axiom / premise
  assume  : {prog : Program} ->       (p : Props) ->
                                      -----------------
                                      prog ⊢ p

  -- Section [2.1]: Conjunction rules
    -- Rule [2.1.1]: conjunction introduction
  ∧-i     : {prog : Program} ->
            {p q : Props} ->
                                      (prog ⊢ p) ->
                                      (prog ⊢ q) ->
                                      ------------
                                      (prog ⊢ (p ∧ q))

    -- Rule [2.1.2]: conjunction elimination
  ∧-e1    : {prog : Program} ->
            {p q : Props} ->
                                      prog ⊢ (p ∧ q) ->
                                      --------------
                                      prog ⊢ p

  ∧-e2    : {prog : Program} ->
            {p q : Props} ->
                                      prog ⊢ (p ∧ q) ->
                                      --------------
                                      prog ⊢ q
  -- Section [2.1337]: Program rules
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
  -- Section [2.2]: Disjunction rules
    -- Rule [2.2.1]: disjunction introduction
  ∨-i1    : {prog : Program} ->
            {p q : Props} -> 
                                      prog ⊢ p ->
                                      ---------------
                                      prog ⊢ (p ∨ q)
  ∨-i2    : {prog : Program} ->
            {p q : Props} -> 
                                      prog ⊢ q ->
                                      ---------------
                                      prog ⊢ (p ∨ q)

    -- Rule [2.2.2]: disjunctive syllogismp
  ∨-e1    : {prog : Program} ->
            {p q : Props} -> 
                                      prog ⊢ (p ∨ q) ->
                                      prog ⊢ (¬ p) ->
                                      ---------------
                                      prog ⊢ q
  ∨-e2    : {prog : Program} ->
            {p q : Props} -> 
                                      prog ⊢ (p ∨ q) ->
                                      prog ⊢ (¬ q) ->
                                      ---------------
                                      prog ⊢ p
    -- Rule [2.2.3]: case anasys
  ca       : {prog : Program} ->
              {p q r : Props} ->
                                      prog ⊢ (p ⊃ r) ->
                                      prog ⊢ (q ⊃ r) -> 
                                      prog ⊢ (p ∨ q) ->
                                      ---------------
                                      prog ⊢ r
    -- Rule [2.2.4]: Constructive dilemma
  cd       : {prog : Program} ->
             {p q r v : Props} ->     prog ⊢ (p ⊃ r) ->
                                      prog ⊢ (q ⊃ v) ->
                                      prog ⊢ (p ∨ q) ->
                                      ---------------
                                      prog ⊢ (r ∨ v)

  -- Section [2.3]: Implication rules
    -- Rule [2.3.1]: implication introduction
  ⊃-i     : {prog : Program} ->
            {p : Props} ->            prog ⊢ (p ⊃ p) -- haha wtf? 
    -- Rule [2.3.2]: modus ponens (impication elimination)
  mp      : {prog : Program} ->
            {p q : Props} ->          prog ⊢ (p ⊃ q) ->
                                      prog ⊢ p ->
                                      ---------
                                      prog ⊢ q
    -- Rule [2.3.3]: modus tollens (conditional elimination)
  mt      : {prog : Program } ->
            {p q : Props} ->          prog ⊢ (p ⊃ q) ->
                                      prog ⊢ (¬ q) ->
                                      ------------
                                      prog ⊢ (¬ p)

    -- Rule [2.3.4]: hypothetical syllogysm (chain rule)
  hs      : {prog : Program } ->
            {p q r : Props} ->        prog ⊢ (p ⊃ q) ->
                                      prog ⊢ (q ⊃ r) ->
                                      ---------------
                                      prog ⊢ (p ⊃ r)
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
    -- Rule [???]: Concatenation control flow, page 472
  ccf : {prog : Program} -> {a b : Label} ->
                                      prog ⊢ (at a ~> after a) ->
                                      prog ⊢ (at b ~> after b) ->
                                      prog ⊢ (comp a b) ->
                                      --------------------
                                      prog ⊢ (at a ~> after b)
    -- Rule [???]: Cobegin control flow
  ccf2 : {prog : Program}
         {a b c : Label} ->           prog ⊢ (at b ~> after b) ->
                                      prog ⊢ (at c ~> after c) ->
                                      prog ⊢ (a =cobegin b wit c) ->
                                      ------------------------------
                                      prog ⊢ (at a ~> after a)
{-
  ◇-p     : {a b : Props}             -> Rule (◇ a)
                                      -> Rule (a ⊃ b)
                                      ---------------
                                      -> Rule (◇ b)


-}

extract : {prog : Program} -> {p : Props} -> prog ⊢ p -> Props
extract {prog} {p} _ = p

