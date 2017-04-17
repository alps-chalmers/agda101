module Playground where

open import Label
open import Data.Nat
open import Data.String
open import LTLRules
open import LTL
open import Program
open import ProgRules

data Proof : LTL → Set where
  assRule : {l₁ l₂ : Label} {x : String} {n : ℕ} → Proof (at l₁) → Stm l₁ (x := n) l₂ → Proof (after l₁ ∧' ("x" ==n n))
  flow    : {l₁ l₂ : Label} {e : Exp} → Proof (after l₁) → Stm l₁ e l₂ → Proof (at l₂)
  -- progR   : {φ : LTL} {l1 l2 : Label} {e : Exp} {s : (Stm l1 e l2)} → ProgRule s ψ → Proof (at l) → Proof ψ
  ltlR    : {φ ψ : LTL} → LTLRule φ ψ → Proof φ → Proof ψ

r0 : Stm (s 0) ("x" := 0) (s 1)
r0 = reg (s 0) ("x" := 0) (s 1)

r1 : Stm (s 1) ("x" := 1) fin
r1 = reg (s 1) ("x" := 1) fin

s0=>s1 : Proof (at (s 0)) → Proof (at (s 1))
s0=>s1 p = flow (ltlR ∧-e₁ (assRule p r0)) r0

s1=>afs1 : Proof (at (s 1)) → Proof (after (s 1))
s1=>afs1 p = ltlR ∧-e₁ (assRule p r1)

proofTerm : Proof (at (s 0)) → Proof (after (s 1))
proofTerm p = s1=>afs1 (s0=>s1 p)

proofBS : Proof ⊥ → Proof (at (s 7))
proofBS = ltlR ⊥-e
