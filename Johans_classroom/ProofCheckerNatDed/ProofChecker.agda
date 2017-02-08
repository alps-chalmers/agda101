module ProofChecker where

open import State
open import Bool
open import Lists
open import MapFold
open import Nat


{-# BUILTIN NATURAL Nat #-}

deadState : State
deadState = st empty empty empty F

{-
  Currently applyRule is not fully implemented, since the ->i case is manually
  configured for this case. This is due to head/tails on lists is troublesome
  when dealing with Maybe. Probabily quite simple fix to make it generic.
-}

applyRule : State -> Rule -> State
applyRule s (->i) = addTruth (popLayer s) (P 2 => (0 eqN 1))  -- TODO HEAD TAILS etc
applyRule s (assume f) = addTruth s f
applyRule s (->e x (x' => y)) = if (( (x eqF x') && isTrue s x) && isTrue s (x' => y)) then addTruth s y else deadState
applyRule s (->e x _) = deadState


giveProof : State -> State
giveProof s = foldl (λ s r → applyRule s r) s (State.proof s)

prove : State -> Bool
prove s = goalReached (foldl (λ s r → applyRule s r) s (State.proof s))

basicProg : List Formula
basicProg = (0 eqN 0) :: ((P zero) :: ((P 2 => P 1) :: ((P 1 => P 0) :: ((P 1 => (0 eqN 1)) :: ((P 1 => (P 0)) :: empty)))))

basicProof : List Rule
basicProof = (assume (P 2)) :: (((->e (P 2) ((P 2) => (P 1)))) :: ((->e (P 1) ((P 1) => (0 eqN 1))) :: ((->i) :: empty)))

basicState : State
basicState = record {
                    init = basicProg
                    ; truths = empty
                    ; proof = basicProof
                    ; goal = (P 2) => (0 eqN 1)
                  }


faultyState : State
faultyState = record {
                    init = basicProg
                    ; truths = empty
                    ; proof = basicProof
                    ; goal = (P 2) => (0 eqN 2)
                  }
