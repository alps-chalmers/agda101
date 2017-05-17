
-- Module used for representing concurrent Procrams in agda.

module Program where

open import Data.Nat
open import Data.Bool
open import Data.String
open import Data.Vec
open import ELTL

-- A process starting at at label i
data Proc : (p : Label) → (l : Label) → Set where
  proc : (p : Label) → (l : Label) → Proc p l

-- Program statement representation.
data Stm : Set where
  _:=n_ : (x : String) → (n : ℕ*) → Stm     -- Nat assignment
  _:=b_ : (x : String) → (b : Bool*) → Stm  -- Bool assignment
  _||_  : ∀{p₁ p₂ a b} → Proc p₁ a → Proc p₂ b → Stm   -- a and b exectued in parallel
  if    : (b : Bool*) → (l : Label) → Stm   -- if-statement
  while : (b : Bool*) → (l : Label) → Stm   -- while-statement
  fin   : ∀{p s} → (pr : Proc p s) → Stm

-- Segment representation. A segment is a labled statement and belongs to a process.
data Seg : Label → Stm → Label → Set where
  seg : (l₁ : Label) → (stm : Stm) → (l₂ : Label) → Seg l₁ stm l₂


--====================== Experimental ======================--

data Stm* : Set where
  seg*   : (l : Label) → (stm : Stm) → Stm*
  block : ∀ {n} → (l : Label) → Vec Stm* n → Stm*

data bot : Set where

record ⊤' : Set where
 tt : ⊤'
 tt = record {}

s1 = seg* (s 1) ("x" :=n nat 5)
s2 = seg* (s 2) ("x" :=n nat 6)
s3 = seg* (s 3) ("x" :=n nat 7)
s4 = seg* (s 4) ("x" :=n nat 8)

s0 : Stm*
s0 = block (s 0) (s1 ∷ s2 ∷ s3 ∷ [])

data _::_∈_ {a} {A : Set a} : {n : ℕ } → A → A → Vec A n → Set a where
  here  : ∀ {n} {x y} {xs : Vec A n} → x :: y ∈ (x ∷ y ∷ xs)
  there : ∀ {n} {x y z} {xs : Vec A n} (xy∈xs : x :: y ∈ xs) → x :: y ∈ (z ∷ xs)


_seq_∈_ : ∀ {n} {A : Set} → (a b : A) → (v : Vec A n) → Set
x seq y ∈ [] = bot
x seq y ∈ xs = {!   !}


test = s1 :: s3 ∈ (s1 ∷ s2 ∷ s3 ∷ [])

{-}
data _∈_ {a} {A : Set a} : A → {n : ℕ} → Vec A n → Set a where
  here  : ∀ {n} {x}   {xs : Vec A n} → x ∈ x ∷ xs
  there : ∀ {n} {x y} {xs : Vec A n} (x∈xs : x ∈ xs) → x ∈ y ∷ xs
-}

--==========================================================--

-- Program representation. Takes a single main process as argument.
data Prog : {p l : Label} → (ps : Proc p l) → ℕ → Set where
  prog : {p l : Label} → (ps : Proc p l) → Prog ps 0
  _⋆_  : ∀{n} {p l : Label} {ps : Proc p l} → (pr : Prog ps n) → (φ : ELTL) → Prog ps (suc n)
