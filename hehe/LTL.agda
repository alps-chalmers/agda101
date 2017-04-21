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

data _⊢_ : Props -> Props -> Set where        -- descriptions of the rules

  assume :                            (p : Props) ->
                                      (q : Props) ->
                                      --------------
                                      p ⊢ q

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


  ∨-i1   : {p q : Props} ->           p ⊢ (p ∨ q)
  ∨-i2   : {p q : Props} ->           q ⊢ (p ∨ q)


  ∨-e    : {p q r : Props} ->       (((p ⊃ r) ∧ 
                                      (q ⊃ r)) ∧ 
                                      (p ∨ q)) ⊢ r

  mp     : {p q r : Props} ->         p ⊢ (q ⊃ r) ->
                                      p ⊢ q ->
                                      --------------
                                      p ⊢ r

  ◇-mp     : {p q r : Props} ->       p ⊢ (q ⊃ r) ->
                                      p ⊢ (◇ q) ->
                                      --------------
                                      p ⊢ (◇ r)

  nd     : {p q : Props} ->         p ⊢ q ->
                                    --------
                                    ⊤ ⊢ (p ⊃ q)

  TL12   : {p q r : Props} ->       p ⊢ (q ~> r) ->
                                    ---------------
                                    p ⊢ (q ⊃ (◇ r))


data _⊨_ : Program -> Props -> Set where
  ⊤-i : {p : Props} ->            (prog : Program) ->
                                  ⊤ ⊢ p ->
                                  ----------------------
                                  prog ⊨ p

      --- assume invariance of a property (safety)
  ▢-i :                           (prog : Program) ->
                                  (p : Props) ->
                                  ------------------
                                  prog ⊨ (p ⊃ (▢ p))

  aar :                           (prog : Program) ->
                                  (l : Label) ->
                                  ------------------------
                                  prog ⊨ (at l ~> after l)
  d-∧-i : {prog : Program}
          {p q : Props} ->        prog ⊨ p ->
                                  prog ⊨ q ->
                                  -----------
                                  prog ⊨ (p ∧ q)
  d-mp : {prog : Program}
         {p q : Props} ->         prog ⊨ (p ⊃ q) ->
                                  prog ⊨ p ->
                                  ---------------
                                  prog ⊨ q

  asr-f :                         (prog : Program) ->
                                  (l : Label) ->
                                  (b : BVar) ->
                                  -------------
                                  prog ⊨ ((at l) ~> ((after l) ∧ ¬ (var b)))


extract-ltl : {prog : Program} -> {p : Props} ->  (prog ⊨ p) -> Props
extract-ltl {prog} {p} _ = p

