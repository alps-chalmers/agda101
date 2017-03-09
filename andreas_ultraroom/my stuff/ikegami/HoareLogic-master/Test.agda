module Test where

open import SET
open import Data.Bool
open import Integer
data Taut : Bool -> Bool -> Set where
import Hoare
import Prim
{-semCond : Bool -> Pred Bool
semCond x = λ x₁ → Bool

tautValid : (b1 b2 : Bool) -> Taut b1 b2 -> (b : Bool) -> semCond b1 b -> semCond b2 b
tautValid = λ b1 b2 x b x₁ → x₁-}

module Hoare' =
  Hoare Bool Bool not ∧ Tautology State SemCond tautValid respNeg respAnd PrimSemComm Axiom axiomValid -- not _∧_ Taut Bool semCond tautValid

open Hoare'
--t : {A : Set} -> {B : Set} -> {a1 a2 : A} -> {b : B} -> HTProof a1 b a2
--t = ?

type : {A : Set} -> A -> Set
type {A} _ = A
