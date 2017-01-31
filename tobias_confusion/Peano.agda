module Peano where

data Nat : Set where
  zero : Nat
  suc :  Nat -> Nat

one : Nat
one = suc zero

--data _even : Nat -> Set where
--  ZERO : zero even
--  STEP : (x : Nat) -> x even -> suc( suc (x)) even

data _even : Nat -> Set where
  ZERO : zero even
  STEP : (x : Nat) -> x even -> suc (suc x) even

proof1 : suc (suc (suc (suc zero))) even
proof1 = STEP (suc (suc zero)) (STEP zero ZERO)



