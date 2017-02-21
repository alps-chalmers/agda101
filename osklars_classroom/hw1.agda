module hw1 where

-- 1

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

  _implies_ : Bool → Bool → Bool
  false implies true = false
  _ implies _ = true

-- 2

-- a

  data Nat : Set where
    O : Nat
    _+1 : Nat → Nat

  _equals_ : Nat → Nat → Bool
  O equals O = true
  O equals n = false
  n equals O = false
  (n +1) equals (m +1) = n equals m

  _odd : Nat → Bool
  O odd = false
  (O +1) odd = true
  ((n +1) +1) odd = n odd

-- b

  _+_ : Nat → Nat → Nat
  O + n = n
  (n +1) + m = (n + m) +1

  _*_ : Nat → Nat → Nat
  O * n = O
  (n +1) * m = m + (n * m)

-- 3

  data Maybe (A : Set) : Set where
    nothing : Maybe A
    just : A → Maybe A

  data List (A : Set) : Set where
    [] : List A
    _,_ : A → List A → List A

  tail : {A : Set} → List A → Maybe (List A)
  tail [] = nothing
  tail (_ , list) = just list

-- 4

-- a

  zipwidth : {A B C : Set} → (A → B → C) → List A → List B → List C
  zipwidth _ _ [] = []
  zipwidth _ [] _ = []
  zipwidth f (a , as) (b , bs) = (f a b) , (zipwidth f as bs)

-- b

  data Vector (A : Set) : Nat → Set where
    0dim : Vector _ O
    _::_ : {n : Nat} → A → Vector A n → Vector A (n +1)

  zipwidthv : {A B C : Set} → {n : Nat} → (A → B → C) → Vector A n → Vector B n → Vector C n
  zipwidthv _ 0dim 0dim = 0dim
  zipwidthv f (a :: as) (b :: bs) = (f a b) :: (zipwidthv f as bs)

  data Pair (A B : Set) : Set where
    pair : A → B → Pair A B

-- 5

-- a

  iterate : {A : Set} → Nat → (A → A) → A → A
  iterate O _ a = a
  iterate (n +1) f a = iterate n f (f a)

  idNat : Nat → Nat
  idNat n = iterate n _+1 O

-- Homework 2

-- 5 cont

  --trans : {A : Set} → {}
