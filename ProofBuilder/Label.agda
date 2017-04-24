{-
  Lables - used in Program and LTL
-}
module Label where

{-***** imported modules *****-}
open import Data.Nat
{-****************************-}

{- a label is used as a reference to a code segment - see more in Program -}
data Label : Set where
  fin : Label → Label -- Represents finised segment
  s   : (n : ℕ) -> Label
