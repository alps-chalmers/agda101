module test where
  data Nat : Set where
    O : Nat
    _+1 : Nat → Nat

  _+_ : Nat → Nat → Nat
  O + a = a
  (a +1) + b  = (a + b) +1

  _*_ : Nat → Nat → Nat
  O * m = O
  (a +1) * b = b + (a * b)

  infixl 41 _*_
  infixl 40 _+_
  

  data _even : Nat → Set where
    AXIOM : O even
    DEF : ∀ x → x even → (x +1) +1 even
    -- DEF is a function that takes two parameters:  (1)a number, and (2)a proof of that number being even, and then returns a proof of that number +2 being even.

  proof : (((O +1) +1) +1) +1 even
  proof = DEF ((O +1) +1) (DEF O AXIOM)



  proof2 : (Type : Set) → Type → Type
  proof2  _ value = value
  
  proof1 : Nat → Nat
  proof1 = proof2 Nat

--Tutorial ch1

  data Twople (A B : Set) : Set where
    T_,_T : A → B → Twople A B
  

  data Image {A B : Set} (f : A → B) : B → Set where
    im : (a : A) → Image f (f a)


  inv : {A B : Set}(f : A → B) → {y : B} → Image f y → A
  inv f (im a) = a
  





  
  

  --_is_ : {A : Set} → A → A → Bool
  --.x is x = true
  --x is _ = false 

  apply : (A : Set) → (B : A → Set) → ((x : A) → B x) → (a : A) → B a
  apply A B f a = f a

  type : {A : Set} → A → Set
  type {A} _ = A

  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x , xs) = f x , map f xs

  join : {A : Set} → List A → List A → List A
  join a [] = a
  join a (b , bs) = join (b , a) bs


 

  


--Learnu ch2
  data _and_ (P Q : Set) : Set where
    firstand : P → Q → (P and Q)

  proof3 : {P Q : Set} → (P and Q) → P
  proof3 (firstand x y) = x

  proof4 : {P Q : Set} → (P and Q) → Q
  proof4 (firstand x y) = y
  

--best exampel data type and function

  data Oskar (P Q : Set) : (a : P) → (b : Q) → Set where
    hej : (a : P) → (b : Q) → Oskar P Q a b

--ETERNAL ASSUMPTION: location x --> ◆ location y where location y = act x(values)
