module Eq where

open import Bool


record Eq (t : Set) : Set where
  field _==_ : t → t → Bool
  _/=_ : t → t → Bool
  a /= b = not ( a == b )

open Eq {{...}}

{-}
_==_ : {t : Set} → {{eqT : Eq t}} → t → t → Bool
_==_ {{eqT}} = Eq._==_ eqT

_/=_ : {t : Set} → {{eqT : Eq t}} → t → t → Bool
_/=_ {{eqT}} = Eq._/=_ eqT
-}
