module ProofBuilder where

open import Label
open import Data.Nat
open import Data.String
-- open import Proofs
open import LTL
open import Program

data Proof : LTL → Set where
  -- Program rules
  assRule : {l₁ l₂ : Label} {x : String} {n : ℕ} → Proof (at l₁) → Stm l₁ (x := n) l₂ → Proof (after l₁ ∧' ("x" ==n n))
  flow    : {l₁ l₂ : Label} {e : Exp} → Proof (after l₁) → Stm l₁ e l₂ → Proof (at l₂)
  parRule : {l l' a b : Label} → Proof (at l) → Stm l (a || b) l' → Proof ((at a) ∧' (at b))
  exitPar : {l l' a b : Label} → Proof ((after a) ∧' (after b)) → Stm l (a || b) l' → Proof (after l ∧' (at l'))
  -- LTL --
  ∧-i     : {φ ψ : LTL} → Proof φ → Proof ψ → Proof (φ ∧' ψ)
  --     : {φ ψ : LTL} → Proof φ ψ → Proof φ → Proof ψ
  ∧-e₁    : {φ ψ : LTL} → Proof (φ ∧' ψ) → Proof φ
  ∧-e₂    : {φ ψ : LTL} → Proof (φ ∧' ψ) → Proof ψ
  ⊥-e     : {φ : LTL} → Proof ⊥ → Proof φ
  in⇒at   : {l : Label} → Proof (in' l) → Proof (at l)
  □⇒~>    : {φ ψ : LTL} → Proof (□(φ ⇒ ψ)) → Proof (φ ~> ψ)
  □-∧-exp : {φ ψ : LTL} → Proof (□(φ ∧' ψ)) → Proof ((□ φ) ∧' (□ ψ))
  □-∨-exp : {φ ψ : LTL} → Proof (□(φ ∨' ψ)) → Proof ((□ φ) ∨' (□ ψ))
  ◇-∧-exp : {φ ψ : LTL} → Proof (◇(φ ∧' ψ)) → Proof ((◇ φ) ∧' (◇ ψ))
  ◇-∨-exp : {φ ψ : LTL} → Proof (◇(φ ∨' ψ)) → Proof ((◇ φ) ∨' (◇ ψ))
  TL5     : {φ ψ : LTL} → Proof ((□ φ) ∧' (□ (φ ⇒ ψ))) → Proof (□ ψ)
  TL6     : {φ : LTL} → Proof ((◇ φ) ∨' (□ (∼ φ)))

s0 : Stm (s 0) ("x" := 0) (s 1)
s0 = reg (s 0) ("x" := 0) (s 1)

s1 : Stm (s 1) ("x" := 1) (s 2)
s1 = reg (s 1) ("x" := 1) (s 2)

s3 : Stm (s 3) ("x" := 5) fin
s3 = reg (s 3) ("x" := 5) fin

s4 : Stm (s 4) ("x" := 6) fin
s4 = reg (s 4) ("x" := 6) fin

s2 : Stm (s 2) ((s 3) || (s 4)) fin
s2 = par (s 2) s3 s4 fin

s0=>s1 : Proof (at (s 0)) → Proof (at (s 1))
s0=>s1 p = flow ( ∧-e₁ (assRule p s0)) s0

s1=>s2 : Proof (at (s 1)) → Proof (at (s 2))
s1=>s2 p = flow ( ∧-e₁ (assRule p s1)) s1

s2=>s3 : Proof (at (s 2)) → Proof (at (s 3))
s2=>s3 p =  ∧-e₁ (parRule p s2)

s2=>s4 : Proof (at (s 2)) → Proof (at (s 4))
s2=>s4 p =  ∧-e₂ (parRule p s2)

s3=>s3' : Proof (at (s 3)) → Proof (after (s 3))
s3=>s3' p =  ∧-e₁ (assRule p s3)

s4=>s4' : Proof (at (s 4)) → Proof (after (s 4))
s4=>s4' p =  ∧-e₁ (assRule p s4)

s2=>s3'∧s4' : Proof (at (s 2)) → Proof ((after (s 3)) ∧' (after (s 4)))
s2=>s3'∧s4' p = ∧-i (s3=>s3' (s2=>s3 p)) (s4=>s4' (s2=>s4 p))

s2=>s2' : Proof (at (s 2)) → Proof (after (s 2))
s2=>s2' p =  ∧-e₁ (exitPar (s2=>s3'∧s4' p) s2)

proof : Proof (at (s 0)) → Proof (after (s 2))
proof p = s2=>s2' (s1=>s2 (s0=>s1 p))
