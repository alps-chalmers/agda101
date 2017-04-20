module LTL where

open import Bool
open import N
--open import CPL
open import Statement
open import Props
open import Label

data Program : Set where
  program : Program

-- Section [2]: Rules
data _⊢_ : Program -> Props -> Set where        -- descriptions of the rules
  
  assume : {prog : Program} ->        (p : Props) ->
                                      --------------
                                      prog ⊢ p

  ∧-e1 : {prog : Program} ->
                                      (p : Props) ->
                                      (q : Props) ->
                                      -----------
                                      prog ⊢ ((p ∧ q) ⊃ p)
  ∧-e2 : {prog : Program} ->
                                      (p : Props) ->
                                      (q : Props) ->
                                      -----------
                                      prog ⊢ ((p ∧ q) ⊃ q)

  ∧-i : {prog : Program} 
        {p q : Props}    ->           prog ⊢ p ->
                                      prog ⊢ q ->
                                      -----------
                                      prog ⊢ (p ∧ q)
  ∧-dist : {prog : Program}           (p : Props) ->
                                      (q : Props) ->
                                      (w : Props) ->
                                      --------------
                                      prog ⊢ ((p ∧ (q ∨ w)) ⊃ ((p ∧ q) ∨ (p ∧ w)))
  TL11 : {prog : Program} ->
         {p q : Props} ->             prog ⊢ ((◇ p) ∧ (▢ q)) ->
                                      --------------------
                                      prog ⊢ (◇ (p ∧ q))
  latticize : {prog : Program} ->
              {a b c : Props} ->      prog ⊢ ◇ (a ∨ b) ->
                                      prog ⊢ (a ⊃ (◇ c)) ->
                                      prog ⊢ (b ⊃ (◇ c)) ->
                                      ----------------
                                      prog ⊢ (◇ c)
  ▢-e : {prog : Program} ->
        {p : Props} ->                prog ⊢ (▢ p) ->
                                      ------------
                                      prog ⊢ p

                              -- asusme invariant
  ▢-i : {prog : Program} ->
        {p : Props} ->                prog ⊢ (p ⊃ (▢ p))

  unsquiggle : {prog : Program} ->
               {p q : Props} ->       prog ⊢ (p ~> q) ->
                                      ---------------
                                      prog ⊢ (▢ (p ⊃ (◇ q)))
    -- TL12, can be proved easily by ▢-e and squiglimination
  TL12 : {prog : Program} ->
         {p q : Props} ->             prog ⊢ (p ~> q) ->
                                      ---------------
                                      prog ⊢ (p ⊃ (◇ q))

  asr-t : {prog : Program} ->
          {l : Label} ->
          {b : BVar} ->               prog ⊢ ((at l) ~> ((after l) ∧ (var b)))

  asr-f : {prog : Program} ->
          {l : Label} ->
          {b : BVar} ->               prog ⊢ ((at l) ~> ((after l) ∧ (¬ (var b))))

  mp    : {prog : Program} ->
          {p q : Props} ->            prog ⊢ (p ⊃ q) ->
                                      prog ⊢ p ->
                                      -----------
                                      prog ⊢ q
  ◇-mp :  {prog : Program} ->
          {p q : Props} ->            prog ⊢ (◇ p) ->
                                      prog ⊢ (p ⊃ q) ->
                                      ------------
                                      prog ⊢ (◇ q)
  -- two truths derived from tTL4a
  TL4a1 : {prog : Program} ->         (p : Props) ->
                                      (q : Props) ->
                                      --------------
                                      prog ⊢ ((▢ (p ∧ q)) ⊃ ((▢ p) ∧ (▢ q)))

  TL4a2 : {prog : Program} ->         (p : Props) ->
                                      (q : Props) ->
                                      --------------
                                      prog ⊢ (((▢ p) ∧ (▢ q)) ⊃ ▢ (p ∧ q))
  TL13 : {prog : Program} ->          (p : Props) ->
                                      --------
                                      prog ⊢ (p ⊃ (◇ p))

extract-ltl : {prog : Program} -> {p : Props} ->  (prog ⊢ p) -> Props
extract-ltl {prog} {p} _ = p

extract-stm : {prog : Program} -> {p : Props} ->  (prog ⊢ p) -> Program
extract-stm {prog} {p} _ = prog
