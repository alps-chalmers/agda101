module Test where

open import Relation.Binary
open import Data.Nat
open import Data.Bool
open import Data.Maybe
open import Data.List.Base
open import Data.List

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
  init : (b : ℕ) → Prog (first b)


t = init zero

test : {p : Prog ((first zero) :: (suc zero))} → ℕ
test = {!   !}
