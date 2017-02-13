module Imports where


  data Bool : Set where
    true : Bool
    false : Bool

  not : Bool → Bool
  not true = false
  not false = true

  _or_ : Bool → Bool → Bool
  true or _ = true
  false or x = x

  _and_ : Bool → Bool → Bool
  false and _ = false
  true and x = x

  if_then_else_ : {A : Set} → Bool → A → A → A
  if true then x else _ = x
  if false then _ else x = x



  data Nat : Set where
    O : Nat
    _+1 : Nat → Nat

  _+_ : Nat → Nat → Nat
  O + n = n
  (n +1) + m = (n + m) +1

  _*_ : Nat → Nat → Nat
  O * n = O
  (n +1) * m = m + (n * m)

  _equals_ : Nat → Nat → Bool
  O equals O = true
  O equals n = false
  n equals O = false
  (n +1) equals (m +1) = n equals m

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

  data List (A : Set) : Set where
    [] : List A
    _,_ : A → List A → List A

  tail : {A : Set} → List A → Maybe (List A)
  tail [] = nothing
  tail (_ , list) = just list

  fold : {A B : Set} → (f : (A → B → A)) → A → List B → A
  fold f a [] = a
  fold f a (x , xs) = fold f (f a x) xs


  

