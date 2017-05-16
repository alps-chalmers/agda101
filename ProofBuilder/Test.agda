module Test where

open import Relation.Binary
open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.List.Base
open import Data.Vec as Vec

data NEL {a} (A : Set a) : (n : ℕ) → Set a where
  first  : A → NEL A (suc zero)
  _::_   : ∀ {i} → NEL A i → A → NEL A (suc i)

data Fin : ℕ → Set where
  zer : {n : ℕ} → Fin (suc n)
  su  : {n : ℕ} → Fin n → Fin (suc n)

find : {A : Set} {n : ℕ} → NEL A n → Fin n → A
find (first x) zer = x
find (x :: xs) zer = xs
find (first x) (su y) = x
find (xs :: x) (su y) = find xs y

data Prog : {n : ℕ} → NEL ℕ n → Set where
  prog : (b : ℕ) → Prog (first b)


t = prog zero

test : {p : Prog ((first zero) :: (suc zero))} → ℕ
test = zero



--------------------------------------------------------------------------------

data bot : Set where

record ⊤' : Set where
 tt : ⊤'
 tt = record {}

even : ℕ → Set
even zero = ⊤'
even (suc (suc x)) = even x
even (suc x) = bot

div2 : (n : ℕ) → even n → ℕ
div2 zero p = zero
div2 (suc zero) ()
div2 (suc (suc x)) p = suc (div2 x p)


apa : ℕ
apa = div2 4 (record {})

vektor : Vec ℕ 3
vektor = zero ∷ (suc zero) ∷ (suc (suc zero)) ∷ []

vekTest : ∀ {n} → (i : ℕ) → (v : Vec ℕ n) → i ∈ v → Set
vekTest x .(x ∷ _) here = ⊤'
vekTest x .(_ ∷ _) (there p) = ⊤'


final = vekTest (suc (suc (suc zero))) vektor {!   !}

{-}
_∈_ : ∀{n} {A : Set} → A → Vec A n → Set
x ∈ Vec.[] ()
x ∈ (y Vec.∷ ys) = {!   !}
-}
