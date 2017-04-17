module Playground where

open import Label
open import Data.Nat
open import Data.String

-- The extended LTL data type
data LTL : Set where
  T' ⊥         : LTL                            -- true & false
  ∼            : (φ : LTL) → LTL                -- not
  □ ◇          : (φ : LTL) → LTL                -- always & eventually
  _∧'_ _∨'_    : (φ : LTL) → LTL → LTL          -- and & or
  _⇒_          : (φ : LTL) → LTL → LTL          -- implies
  _~>_         : (φ : LTL) → (ψ : LTL) → LTL    -- leads to - (P ~> Q) ≡ □(P ⊂ ◇Q)
  at in' after : (l : Label) → LTL              -- at, in & after a code segment - extended
                                                -- from Owiki & Lamport
  _==n_        : (x : String) → (n : ℕ) → LTL     -- Nat variable x has the value n
  _==b_        : (x : String) → (y : String) → LTL  -- Bool variable x has the value of y
  isTrue       : (x : String) → LTL               -- Variable x has the value -- true

data Exp : Set where
  todo : Exp
  _:=_ : (x : String) → (n : ℕ) → Exp

data Stm : Label → Exp → Label → Set where
  reg : (l₁ : Label) → (e : Exp) → (l₂ : Label) → Stm l₁ e l₂
  par : {l₁ l₂ x y : Label} → Stm l₁ todo x → Stm l₂ todo y → Stm l₁ todo l₂

data Proof : LTL → Set where
  axiom   : (φ : LTL) → Proof φ
  assRule : {l₁ l₂ : Label} {x : String} {n : ℕ} → Proof (at l₁) → Stm l₁ (x := n) l₂ → Proof (after l₁ ∧' ("x" ==n n))
  flow    : {l₁ l₂ : Label} {e : Exp} → Proof (after l₁) → Stm l₁ e l₂ → Proof (at l₂)
  ∧-e₁    : {φ ψ : LTL} → Proof (φ ∧' ψ) → Proof φ
  ∧-e₂    : {φ ψ : LTL} → Proof (φ ∧' ψ) → Proof φ

-- r0 : Stm (s 1) ()

r1 : Stm (s 0) ("x" := 0) (s 1)
r1 = reg (s 0) ("x" := 0) (s 1)

init : (φ : LTL) → Proof φ
init x = axiom x

step1 : Proof (at (s 0)) → Proof ((after (s 0)) ∧' ("x" ==n 0))
step1 p = assRule p r1

proof : Proof (at (s 0)) → Proof (at (s 1))
proof p = flow (∧-e₁ (assRule p r1)) r1
