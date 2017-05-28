{-
  Lables - used in Program and LTL
-}
module Label where

{-***** imported modules *****-}
open import N
{-****************************-}

{- a label is used as a reference to a code segment - see more in Program -}
data Label : Set where
  l : N -> Label

