{-
  Program representation, used in Translator. For more on the frequently used
  labels, see Label.
-}
module Program where

{-***** imported modules *****-}
open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.String
open import Label
{-****************************-}

{-
  Data type for integer variables
-}
data NVar : Set where
  vN : String → NVar  -- Natural variable (indexed over ℕ)

{-
  Data type for boolean variables
-}
data BVar : Set where
  vB : String → BVar  -- Boolean variable (indexed over ℕ)

{-
  Data type for expressions regarding natural numbers/variables
-}
data ExpN : Set where
  nat : ℕ → ExpN      -- expression for ℕ
  nVar : NVar → ExpN  -- expression for natural variables, currently not
                      -- supported since no memory is implemented

{-
  Data type for expressions regarding booleans
-}
data ExpB : Set where
  bool : Bool → ExpB  -- expression for booleans
  bVar : BVar → ExpB  -- expression for boolean variables, currently not
                      -- supported since no memory is implemented

{-
  Data type for expressions overall, probably redundant
-}
data Exp : Set where
  expN : ExpN → Exp                          -- Wrapper for ExpN
  expB : ExpB → Exp                          -- Wrapper for ExpB
  _<?_ _<=?_ _>?_ _>=?_ : ExpN → ExpN → Exp  -- Might as well be constructors in
                                             -- ExpB
  _==n_ : ExpN → ExpN → Exp                  -- As above
  _==b_ : ExpB → ExpB → Exp                  -- As above

{-
  Data type for statements, right now we only use atomic assignments
-}
data Stm : Set where
  -- <_>:=n<_> : NVar → ExpN → Stm  -- Non-atomic assignment for natural variables
  <_:=n_> : NVar → ℕ → Stm    -- Atomic assignment for natural variables
  -- <_>:=b<_> : BVar → ExpB → Stm  -- Non-atomic assignment for boolean variables
  <_:=b_> : BVar → ExpB → Stm    -- Atomic assignment for boolean variables
  -- wait : Exp → Stm               -- Awaits an expression to become true,
                                 -- currently not used

{-
  Data type for a code segment. Can be a regular segment, block of code
  segments, a par statement (cobegin/coend) as well as while loops and if
  statements.
-}
data Seg : Set where
  seg : Label → Stm → Seg              -- Regular segment, labels a statement
  block : Label → List Seg → Seg       -- Block, labels a list of segments
  par : Label → List Seg → Seg         -- Parallel segment, labels a list of
                                       -- segments where each elements are run
                                       -- in parallel
  while if : Label → ExpB → Seg → Seg  -- While loops and if statement segments

{-
  Label extraction function for each segment constructor
-}
label : Seg → Label
label (seg x x₁) = x       -- Extracts the label from regular segment
label (block x x₁) = x     -- Extracts the label from a block segment
label (par x x₁) = x       -- Extracts the label from a prallel segment
label (while x x₁ x₂) = x  -- Extracts the label from a while loop segment
label (if x x₁ x₂) = x     -- Extracts the label from an if statement segment

{-
  Record for program, contains a main segment, should be a block with the rest
  of the program's segments
-}
record Prog : Set where
  constructor prog  -- Constructor used to make a program
  field
    main : Seg      -- The actual code of the program, should be a block segment
