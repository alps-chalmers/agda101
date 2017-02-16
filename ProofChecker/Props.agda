module Props where

open import Nat

data Props : Set where
  T F : Props
  p : Nat -> Props
  ~_ : Props -> Props
  _^_ _v_ _=>_ : Props -> Props -> Props
  <>_ []_ : Props -> Props
