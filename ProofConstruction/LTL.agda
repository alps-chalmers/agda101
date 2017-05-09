module LTL where

open import Bool
open import N
open import Statement
open import Props
open import Label

import Labels


-- Section [2]: Rules

data _⊢_ : Props -> Props -> Set where        -- descriptions of the rules


  identity :                          (p : Props) ->
                                      --------------
                                      p ⊢ p

  ∧-i    : {p q r : Props} ->         p ⊢ q ->
                                      p ⊢ r ->
                                      -----------
                                      p ⊢ (q ∧ r)

  ∧-e1   : {p q r : Props} ->         p ⊢ (q ∧ r) ->
                                      p ⊢ q
  ∧-e2   : {p q r : Props} ->         p ⊢ (q ∧ r) ->
                                      p ⊢ r


  ∨-i1   : {p q : Props} ->           p ⊢ q ->
                                      (r : Props) ->
                                      --------
                                      p ⊢ (q ∨ r)
  ∨-i2   : {p q : Props} ->           p ⊢ q ->
                                      (r : Props) ->
                                      --------
                                      p ⊢ (r ∨ q)


  ca : {p q r s : Props} ->           p ⊢ (q ⊃ s) ->
                                      p ⊢ (r ⊃ s) ->
                                      p ⊢ (q ∨ r) ->
                                      ---------------
                                      p ⊢ s

  mp     : {p q r : Props} ->         p ⊢ (q ⊃ r) ->
                                      p ⊢ q ->
                                      --------------
                                      p ⊢ r

  ◇-mp     : {p q r : Props} ->       p ⊢ (▢ (q ⊃ r)) ->
                                      p ⊢ (◇ q) ->
                                      --------------
                                      p ⊢ (◇ r)

  nd     : {p q : Props} ->         p ⊢ q ->
                                    --------
                                    ⊤ ⊢ (p ⊃ q)

          --- things that are tautologically true are always true
  ▢-⊤    : {p : Props} ->           ⊤ ⊢ p ->
                                    --------
                                    ⊤ ⊢ ▢ p

  TL12   : {p q r : Props} ->       p ⊢ (q ~> r) ->
                                    ---------------
                                    p ⊢ (q ⊃ (◇ r))

      -- palla bevisa lul
  TL14 : {p q r s : Props} ->       p ⊢ (q ⊃ ◇ (▢ r)) ->
                                    p ⊢ (q ⊃ ◇ (▢ s)) ->
                                    --------------------
                                    p ⊢ (q ⊃ ◇ (▢ (r ∧ s)))

  TL4 : {p q r : Props} ->          p ⊢ (▢ (q ∧ r)) ->
                                    -------------------
                                    p ⊢ ((▢ q) ∧ (▢ r))

  imp-eq1 : {p q r : Props} ->      p ⊢ (q ⊃ r) ->
                                    ------------
                                    p ⊢ ((¬ q) ∨ r)

  imp-eq2 : {p q r : Props} ->      p ⊢ ((¬ q) ∨ r) ->
                                    ------------
                                    p ⊢ (q ⊃ r)

  ⊃-comb : {p q r s : Props} ->       p ⊢ (q ⊃ r) ->
                                    p ⊢ (q ⊃ s) ->
                                    --------------
                                    p ⊢ (q ⊃ (r ∧ s))


  hs : {p q r s : Props} ->         p ⊢ (q ⊃ r) ->
                                    p ⊢ (r ⊃ s) ->
                                    ---------------
                                    p ⊢ (q ⊃ s)

  ◇-hs : {p q r s : Props} ->       p ⊢ (q ⊃ (◇ r)) ->
                                    p ⊢ (r ⊃ (◇ s)) ->
                                    -------------------
                                    p ⊢ (q ⊃ (◇ s))

  weaken : {p q r : Props} ->       (p ∧ q) ⊢ r ->
                                    --------------
                                    p ⊢ (q ⊃ r)

  ▢-e : {p q : Props} ->            p ⊢ (▢ q) ->
                                    -------------
                                    p ⊢ q

  ◇-i : {p q : Props} ->            p ⊢ q ->
                                    -----------
                                    p ⊢ (◇ q)

  ⊤-i : {q : Props} ->               ⊤ ⊢ q ->
                                    (p : Props) ->
                                    --------------
                                    p ⊢ q


data _⊨_ : Program -> Props -> Set where
  d-⊤-i : {p : Props} ->          (prog : Program) ->   -- verified [x]
                                  ⊤ ⊢ p ->
                                  ----------------------
                                  prog ⊨ p

      --- assume invariance of a property (safety)
  ▢-i :                           (prog : Program) ->   -- verified [x]
                                  (p : Props) ->
                                  ------------------
                                  prog ⊨ (▢ (p ⊃ (▢ p)))

  aar :                           (prog : Program) ->   -- verified [x]
                                  (l : Label) ->
                                  ------------------------
                                  prog ⊨ (at l ~> after l)
  d-∧-i : {prog : Program}
          {p q : Props} ->        prog ⊨ p ->           -- verified [x]
                                  prog ⊨ q ->
                                  -----------
                                  prog ⊨ (p ∧ q)
  d-mp : {prog : Program}
         {p q : Props} ->         prog ⊨ (p ⊃ q) ->     -- verified [x]
                                  prog ⊨ p ->
                                  ---------------
                                  prog ⊨ q

  asr-f :                         (prog : Program) ->   -- verified [x]
                                  (l : Label) ->
                                  (b : BVar) ->
                                  -------------
                                  prog ⊨ ((at l) ~> ((after l) ∧ ¬ (var b)))

  assume :                        (prog : Program) ->   -- verified [x]
                                  (p : Props) ->
                                  --------------
                                  prog ⊨ p

  after-while :                   (prog : Program) ->   -- verified [x]
                                  (l1 : Label) ->
                                  (l2 : Label) ->
                                  -----------------
                                  prog ⊨ ▢ ((after l1 ⊃ (at l2)))

  inside-while :                  (prog : Program) ->   -- verified [ ]
                                  (l : Label) ->
                                  (p : Props) ->
                                  -------------
                                  prog ⊨ ((inside l) ⊃ p)

  wer :                           (prog : Program) ->   -- verified [ ]
                                  (l : Label) ->
                                  (p : Props) ->
                                  --------------
                                  prog ⊨ (▢ (((at Labels.c) ∧ (▢ (¬ p))) ⊃
                                          (◇ (after Labels.c))))

∧-comm : {p q r : Props} -> p ⊢ (q ∧ r) -> p ⊢ (r ∧ q)
∧-comm proof = ∧-i (∧-e2 proof) (∧-e1 proof)

make-implication : (p : Props) -> (q : Props) -> p ⊢ (q ⊃ p)
make-implication p q = imp-eq2 (∨-i2 (identity p) (¬ q))

extract-ltl : {prog : Program} -> {p : Props} ->  (prog ⊨ p) -> Props
extract-ltl {prog} {p} _ = p

apply-proof : {prog : Program} {p q : Props} -> prog ⊨ p ->
                                                p ⊢ q ->
                                                ------------
                                                prog ⊨ q

apply-proof {prog} {p} {q} sat proof = d-mp (d-⊤-i prog (nd proof)) sat






