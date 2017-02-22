module LTL where

-- infixr 0 _⇒_
-- infixr 5 _∨_

data TPred : Set where
  T F : TPred
