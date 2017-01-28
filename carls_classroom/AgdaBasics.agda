module AgdaBasics where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)

_*_ : Nat -> Nat -> Nat
zero * m = zero
suc n * m = m + n * m

_or_ : Bool -> Bool -> Bool ->
false or x = x
true or _ = true

if_then_else : {A : Set} -> Bool -> A -> A -> A
if true then x else y = x
if false then x else y = y

infixl 60 _*_
infixl 40 _+_
infixr 20 _or_
infix 5 if_then_else_

infixr 40 _::_
data List (A : Set) : Set where
[] : List A
_::_ : A -> List A -> List A

id : {A : Set} -> A -> A
id x = x

zero' : Nat
zero' = id Nat zero

on : (A : Set) -> (B : A -> Set) ->
     ((x : A) -> B x) -> (a : A) -> B a
on A B f a = f a

_o_ : {A : Set} -> {B : A -> Set} -> {C : (x : A) -> B x -> Set} ->
      (f : {x : A} -> (y : B x) -> C x y) -> (g : (x : A) -> B x) -> (x : A) ->
      C x (g x)
(f o g) x = f (g x)

map : {A B : Set} -> (A -> B) -> List A -> List B
map f [] = []
map f (x :: xs) = f x :: map f xs

_++_ : {A : Set} -> List A -> List A -> List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

data Vec (A : Set) : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

head : {A : Set} -> {n : Nat} -> Vec A (suc n) -> A
head (x :: xs) = x

vmap : {A B : Set} -> {n : Nat} -> (A -> B) -> Vec A n -> Vec B n
vmap f [] = []
vmap f (x :: xs) = f x :: vmap f xs

data Vec2 (A : Set) : Nat -> Set where
  nil : Vec2 A zero
  cons : (n : Nat) -> A -> Vec2 A n -> Vec2 A (suc n)

vmap2 : {A B : Set} -> (n : Nat) -> (A -> B) -> Vec2 A n -> Vec2 B n
vmap2 .zero f nil = nil
vmap2 .(suc n) f (cons n x xs) = cons n (f x) (vmap2 n f xs)

vmap3 : {A B : Set} -> (n : Nat) -> (A -> B) -> Vec2 A n -> Vec2 B n
vmap3 zero f nil = nil
vmap3 (suc n) f (cons .n x xs) = cons n (f x) (vmap3 n f xs)

data Image_€_ {A B : Set}(f : A -> B) : B -> Set where
  im : (x : A) -> Image f € f x

inv : {A B : Set} -> (f : A -> B) -> (y : B) -> Image f € y -> A
inv f .(f x) (im x) = x

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc : {n : Nat} -> Fin n -> Fin (suc n)

magic : {A : Set} -> Fin zero -> A
magic ()

data Empty : Set where
  empty : Fin zero -> Empty

magic' : {A : Set} -> Empty -> A
magic' (empty())

_!_ : {n : Nat} -> {A : Set} -> Vec A n -> Fin n -> A
[] ! ()
(x :: xs) ! fzero = x
(x :: xs) ! (fsuc i) = xs ! i

tabulate : {n : Nat} -> {A : Set} -> (Fin n -> A) -> Vec A n
tabulate {zero} f = []
tabulate {suc n} f = f fzero :: tabulate (f o fsuc)

data False : Set where
record True : Set where

trivial : true
trivial = _

isTrue : Bool -> Set
isTrue true = True
isTrue false = False

_<_ : Nat -> Nat -> Bool
_ < zero = false
zero < suc n = true
suc m < suc n = m < n

length : {A : Set} -> List A -> Nat
length [] = zero
length (x :: xs) = suc (length xs)

lookup : {A : Set} -> (xs : List A)(n : Nat) -> isTrue (n < length xs) -> A
lookup [] n ()
lookup (x :: xs) zero p = x
lookup (x :: xs) (suc n) p = lookup xs n p

data _==_ {A : Set}(x : A) : A -> Set where
  refl : x == x

data _<=_ : Nat -> Nat -> Set where
  leq-zero : {n : Nat} -> zero <= n
  leq-suc : {m n : Nat} -> m <= n -> suc m <= suc n

leq-trans : {l m n : Nat} -> l ≤ m -> m ≤ n -> l ≤ n
leq-trans leq-zero _ = leq-zero
leq-trans (leq-suc p) (leq-suc q) = leq-suc (leq-trans p q)
