
-- Module used for representing concurrent Procrams in agda.

module CPL where

open import Data.Nat
open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.String
open import ELTL
open import Absurdity

data Block : Set where
  first : String → Block
  _::_  : Block → String → Block

-- Program statement representation.
data Stm : Set where
  _:=n_ : (x : String)  → (n : ℕ*)      → Stm
  _:=b_ : (x : String)  → (b : Bool*)   → Stm
  block : (b : Block)                   → Stm
  _||_  : (s₁ : String) → (s₂ : String) → Stm   -- a and b exectued in parallel
  if    : (b : Bool*)   → (l : String)  → Stm   -- if-statement
  while : (b : Bool*)   → (l : String)  → Stm   -- while-statement
  swapN : (x : String)  → (y : String)  → Stm
  swapB : (x : String)  → (y : String)  → Stm

data Stm* : String → Stm → Set where
  stm   : (l : String) → (st : Stm) → Stm* l st

data Prog : ∀ {l s} → Stm* l s → ℕ → Set where
  prog : ∀{l s} → (st : Stm* l s) → Prog st 0
  _⋆_  : ∀{l s n} {st : Stm* l s} → (p : Prog st n) → (φ : ELTL) → Prog st (suc n)


_∈*_ : String → Block → Set
x ∈* first y = if x == y then T' else ⊥'
x ∈* (ys :: y) = if x == y then T' else (x ∈* ys)

{-
_∈s_ : ∀ {l} {st : Stm} → String → Stm* l st → Set
x ∈s stm l (block b) = {!   !}
x ∈s stm l st = if (x == l) then T' else (x ∈s {! stm   !})
-}

_∈_ : ∀ {l₁ l₂ s₁ s₂ n} {s* : Stm* l₁ s₁} → Stm* l₂ s₂ → Prog s* n → Set
stm l₁ st₁ ∈ prog (stm l (block b)) = if (l == l₁) then T' else (l ∈* b)
stm l₁ st₁ ∈ prog (stm l _) = if (l == l₁) then T' else ⊥'
st ∈ (y ⋆ φ) = st ∈ y

_seq_∈_ : String → String → Block → Set
x seq y ∈ first _ = ⊥'
x seq y ∈ (first x* :: y*) = if ((x == x*) Bool.∧ (y == y*)) then T' else ⊥'
x seq y ∈ ((b :: x*) :: y*) = if ((x == x*) Bool.∧ (y == y*)) then T' else x seq y ∈ (b :: x*)

_head_ : String → Block → Set
str head (first x) = if (x == str) then T' else ⊥'
str head (b :: x)  = if x == str then ⊥' else str head b

fin : Block → String → Set
fin (first x) str = if x == str then T' else ⊥'
fin (b :: x) str = if x == str then T' else ⊥'
