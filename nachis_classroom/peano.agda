module peano where
data ℕ : Set where
  zero : ℕ 
  suc : ℕ → ℕ

  -- operations

_+_ : ℕ → ℕ → ℕ
zero + zero = zero
zero + n = n
(suc n) + n′ = suc (n + n′)  -- use ′ to input ′.

one : ℕ
one = suc zero

two : ℕ
two = suc one

three : ℕ
three = suc two

four : ℕ
four = suc three

-- think of even as a predicate / proof
data even : ℕ → Set where
  ZERO : even zero
  STEP : ∀ x → even x → even (suc (suc x))
  STEP' : {x : ℕ} → even x → even (suc (suc x)) 

eight : ℕ
eight = four + four

proof : even four
proof = STEP two (STEP zero ZERO)

proof' : even four
proof' = STEP' (STEP' ZERO)
