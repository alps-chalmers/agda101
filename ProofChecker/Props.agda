module Props where

open import Nat
open import Bool

data Props : Set where
  T F : Props
  p : Nat -> Props
  ~_ : Props -> Props
  _^_ _v_ _=>_ _=~>_ : Props -> Props -> Props
  <>_ []_ : Props -> Props
