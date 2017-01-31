module Identity where

open import Nat

{-
We shall now define the set I A a a' containing proofs that a, a' : A are identical. We call this the identity set. The nature of identity sets is a hot topic (cf "homotopy type theory") but the basic idea in intuitionistic type theory is that there is only one way to construct a proof of an identity: a and a' must be *the same* (modulo simplification). Hence we define the identity sets as a data type with one constructor:
-}

data I (A : Set) (a : A) : A → Set where
  refl : I A a a

{-
We get a more familiar looking notation if we use the infix sign ≡ and make the type A implicit:
-}

data _≡_ {A : Set} (a : A) : A → Set where
  refl : a ≡ a

1+1=2 : 1 + 1 ≡ 2
1+1=2 = refl

{-
When we case-split (C-c C-c) a proof c : I A a a', Agda replaces c by the only possible constructor refl, and unifies a and a'. We can see how this works by proving that identity is a symmetric relation:
-}

sym : {A : Set} → {a₁ a₂ : A} → a₁ ≡ a₂ → a₂ ≡ a₁
sym refl = refl

{-
Exercise: prove transitivity by doing pattern matching in both arguments:

trans : {A : Set} → {a₁ a₂ a₃ : A} → a₁ ≡ a₂ → a₂ ≡ a₃ → a₁ ≡ a₃
trans p₁ p₂ = {!!}

We can also prove the general rule of identity elimination, the rule that states that we can substitute identical elements for each other. If a property is true for a₂, then it's
also true for any a₁ equal to a₂
-}

subst : {A : Set} -> {P : A → Set} → {a₁ a₂ : A} → a₁ ≡ a₂ -> P a₂ -> P a₁
subst refl q = q

{-
Prove that functions map equal inputs to equal outputs
-}

cong : {A B : Set} → {a₁ a₂ : A} → (f : A → B)
  → a₁ ≡ a₂
  → f a₁ ≡ f a₂
cong f refl = refl

{-
Exercise: prove symmetry and transitivity using subst but without using pattern matching!
-}
