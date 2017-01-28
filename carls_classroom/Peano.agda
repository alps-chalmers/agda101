module Peano where

data ℕ : Set where
  zero : ℕ
  suc : ℕ -> ℕ

_+_ : ℕ -> ℕ -> ℕ
zero + zero = zero
zero + x = x
(suc x) + y = suc (x + y)

data _even : ℕ -> Set where
  ZERO : zero even
  STEP : (x : ℕ) -> x even -> suc (suc x) even

proof₁ : suc (suc (suc (suc zero))) even
proof₁ = STEP (suc (suc zero)) (STEP zero ZERO)

-- proof₂ : (suc (suc zero)) even -> (suc (suc zero)) even
-- proof₂ v = v

proof₂′ : (A : Set) -> A -> A
proof₂′ _ x = x

proof₂ : (suc (suc zero)) even -> (suc (suc zero)) even
proof₂ = proof₂′ ((suc (suc zero)) even)

data _∧_ (P : Set) (Q : Set) : Set where
  ∧-intro : P → Q → (P ∧ Q)

proof₃ : {P Q : Set} → (P ∧ Q) → P
proof₃ (∧-intro p q) = p

_⇔_ : (P : Set) → (Q : Set) → Set
a ⇔ b = (a → b) ∧ (b → a)

∧-comm′ : {P Q : Set} → (P ∧ Q) → (Q ∧ P)
∧-comm′ (∧-intro p q) = ∧-intro q p

∧-comm : {P Q : Set} → (P ∧ Q) ⇔ (Q ∧ P)
∧-comm = ∧-intro ∧-comm′ ∧-comm′

∧-assoc₁ : {P Q R : Set} → ((P ∧ Q) ∧ R) → (P ∧ (Q ∧ R))
∧-assoc₁ (∧-intro (∧-intro p q) r) = ∧-intro p (∧-intro q r)

∧-assoc₂ : { P Q R : Set } → (P ∧ (Q ∧ R)) → ((P ∧ Q) ∧ R)
∧-assoc₂ (∧-intro p (∧-intro q r)) = ∧-intro (∧-intro p q) r

∧-assoc : { P Q R : Set } → ((P ∧ Q) ∧ R) ⇔  (P ∧ (Q ∧ R))
∧-assoc = ∧-intro ∧-assoc₁ ∧-assoc₂

data _∨_ (P Q : Set) : Set where
  ∨-intro₁ : P → P ∨ Q
  ∨-intro₂ : Q → P ∨ Q

∨-elim : {A B C : Set} → (A → C) → (B → C) → (A ∨ B) → C
∨-elim ac bc (∨-intro₁ a) = ac a
∨-elim ac bc (∨-intro₂ b) = bc b

∨-comm′ : {P Q : Set} → (P ∨ Q) → (Q ∨ P)
∨-comm′ (∨-intro₁ p) = ∨-intro₂ p
∨-comm′ (∨-intro₂ q) = ∨-intro₁ q

∨-comm : {P Q : Set} → (P ∨ Q) ⇔ (Q ∨ P)
∨-comm = ∧-intro ∨-comm′ ∨-comm′

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥
