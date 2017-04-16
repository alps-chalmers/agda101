{-
  Does the actual verifying of proofs. Contains data types for Proofs and
  functions for verification
-}
module ProofChecker where

{-***** imported modules *****-}
open import Data.Bool
open import ValidProof
open import Data.List as List
open import Data.Nat
open import Props
open import Program
open import LTL
open import Translator
open import Label
open import Rules
open import Function
open import Data.String as String renaming (_++_ to _s++_)
open import LTLRule
{-****************************-}

{-
  Data type for proof steps used in a proof
  -----TODO Add condition rule for branching.-----
-}
data ProofStep : Set where
  pStep : Rule → ProofStep
    -- Regular proof step, uses a rule (see Rules)
  branch : Rule → List ProofStep → List ProofStep → ProofStep
    -- A branch step, used when multiple assumptions has to end up with the
    -- same conclusion. Functions as two sub-proofs

{-
  Data type for a proof
-}
data Proof : Set where
  proof : List ProofStep → Proof -- The proof takes a list of proof steps

{-# TERMINATING #-} --used to guarantee that no infinite loop will occur

{-
  takeStep tries to apply the rule for a step in the proof.
  takeStep : Program translation → Proof step → Current truth → Resulting LTL
-}
takeStep : List TransRel → ProofStep → ValidProof → ValidProof
takeStep _ _ (no err) = no err
  -- If something invalid is passed (see ValidProof), return the ValidProof
  -- 'no' with error message 'err' (see ValidProof)
takeStep prg (pStep r) (yes φ) = applyRule prg φ r
  -- If a regular proofstep is passed with a valid LTL formulae, pass
  -- information to applyRule (see Rules) and returns the result
takeStep prg (branch x b₁ b₂) (yes φ) = case res1 of λ -- Return depends on res1
                                                       -- and res2
  { (yes ψ₁) → case res2 of λ  -- First branch is valid, check result of second
    { (yes ψ₂) → if isEq ψ₁ ψ₂ then yes ψ₁ else no ("Mismatch of conclusions " s++ (pLTL ψ₁) s++ " and " s++ (pLTL ψ₂))
      -- If second branch is valid as well, check if they have the same
      -- conclusion
    ; err → err  -- Second branch invalid, return error message 'err'
    }
  ; err  → err   -- First branch invalid, return error message 'err'
  }
  where
    res1 = foldl (λ Γ step → takeStep prg step Γ) (yes φ) b₁
      -- Accumulates the result of takeStep on the first branch
    res2 = foldl (λ Γ step → takeStep prg step Γ) (yes φ) b₂
      -- Accumulates the result of takeStep on the second branch

{-
  Checks whether a given proof holds for a given program.
  proofCheck : program translation → proof → goal → known → Resulting Boolean
-}
proofCheck' : List TransRel → Proof → LTL → LTL → ValidProof
proofCheck' _ _ T' _ = yes T'
  -- If passed something true, return that it is valid because it's true
proofCheck' _ _ ⊥ _ = no  "⊥ always false."
  -- If passed something false, return that it is invalid because it's false
proofCheck' rels pr (□ φ) Γ = no "TODO □"
  -- Currently not implemented
  -- TODO add box, maybe prove termination and still holds?
proofCheck' rels pr (φ ⇒ ψ) _ = proofCheck' rels pr ψ φ
  -- If passed an implication, replace what is known with LHS of implication and
  -- pass on to itself
proofCheck' rels (proof stps) (◇ φ) Γ = case res of λ
  -- If passed an eventually proof, return depends on res
  { (yes ψ) → if isEq φ ψ then yes (◇ φ) else no ("Wrong conclusion, " s++ (pLTL φ) s++ " is not the same as " s++ (pLTL ψ) s++ ".")
    -- If the proof is valid and concludes the goal, return that it is valid,
    -- else return that it is invalid with an error message
  ; err → err
    -- If the proof is invalid, return that it is invalid with an error message
  }
  where res = foldl (λ t stp → takeStep rels stp t) (yes Γ) stps
    -- res accumulates the result of takeStep on the proof passed
proofCheck' rels _ φ Γ = if (isEq φ Γ) then yes φ else no ((pLTL φ) s++ " is not true in the initial state.")
  -- If the goal and what is known if identical, return that it is valid, else
  -- return an error message

{-
  takes a program, custom rules, a proof, a goal and a truth. Returns wether or
  not the proof is valid given the rest of the passed input
-}
proofCheck : Prog → List TransRel → Proof → LTL → LTL → ValidProof
proofCheck pr rels g Γ = proofCheck' ((translate pr) List.++ rels) g Γ
  -- Passes modified input to ProofCheck' (see above)




{-***** test stuff *****-}

update' : (LTL → LTL → Bool) → List LTL → LTL → List LTL
update' f [] ltl = []
update' f (x ∷ ltls) ltl = if (f x ltl) then (ltl ∷ ltls) else x ∷ (update' f ltls ltl)

update : ℕ → List LTL → LTL → List LTL
update x [] ltl = []
update zero (x₁ ∷ ltls) ltl = ltl ∷ ltls
update (suc x) (x₁ ∷ ltls) ltl = x₁ ∷ (update x ltls ltl)

is∧ : LTL → Bool
is∧ (ltl₁ ∧' ltl₂) = true
is∧ _ = false


expand∧₁ : (LTL → LTL → Bool) → List LTL → LTL → List LTL
expand∧₁ f [] ltl = []
expand∧₁ f ((ltl₁ ∧' ltl₂) ∷ ltls) ltl = if (f (ltl₁ ∧' ltl₂) ltl) then (ltl₁ ∷ (ltl₂ ∷ ltls)) else (ltl₁ ∧' ltl₂) ∷ (expand∧₁ f ltls ltl)
expand∧₁ f (x ∷ ltls) ltl = x ∷ (expand∧₁ f ltls ltl)



expand∧₂ : (LTL → LTL → Bool) → List LTL → LTL → List LTL
expand∧₂ f [] ltl = []
expand∧₂ f ((ltl₁ ∧' ltl₂) ∷ ltls) ltl = if (f (ltl₁ ∧' ltl₂) ltl) then (expand∧₂ f (ltl₁ ∷ []) ltl₁) ++ ((expand∧₂ f (ltl₂ ∷ []) ltl₂) ++ ltls) else (ltl₁ ∧' ltl₂) ∷ (expand∧₂ f ltls ltl)
expand∧₂ f (x ∷ ltls) ltl = x ∷ (expand∧₂ f ltls ltl)



expand_In_ : LTL → List LTL → List LTL
expand ltl In ltls = if is∧ ltl then expand∧₂ isEq ltls ltl else ltls


ltls : List LTL
ltls = ⊥ ∷ ((at (s 0)) ∧' ((at (s 1)) ∧' (at (s 2))) ∷ (⊥ ∷ []))


{-***** truth stuff *****-}

data Truths : Set where
  truths : List LTL → Truths

innitTruths : List LTL → Truths
innitTruths ltls = truths ltls

listTruths : Truths → List LTL
listTruths (truths x) = x

□truth : LTL → Truths → Truths
□truth ltl₁ (truths []) = truths []
□truth ltl₁ (truths (ltl₂ ∷ ltls)) = if (isEq ltl₁ ltl₂) then truths ((□ ltl₂) ∷ ltls) else truths ((ltl₂ ∷ []) ++  listTruths (□truth ltl₁ (truths ltls)))

is□ : LTL → Bool
is□ (□ _) = true
is□ _ = false

un□truth : LTL → Truths → Truths
un□truth (□ ltl₁) (truths []) = truths []
un□truth (□ ltl₁) (truths (ltl₂ ∷ ltls)) = if (isEq (□ ltl₁) ltl₂) then truths (ltl₁ ∷ ltls) else truths ((ltl₂ ∷ []) ++ (listTruths (un□truth (□ ltl₁) (truths ltls))))
un□truth _ tr = tr

rm : LTL → Truths → Truths
rm ltl₁ (truths []) = truths []
rm ltl₁ (truths (ltl₂ ∷ ltls)) = if (isEq ltl₁ ltl₂) then (truths ltls) else (truths ((ltl₂ ∷ []) ++ (listTruths (rm ltl₁ (truths ltls)))))

rm' : List LTL → Truths → Truths
rm' [] tr = tr
rm' (ltl ∷ ltls) tr = rm' ltls (rm ltl tr)

shouldStay : LTL → Bool
shouldStay (at _) = true
shouldStay (in' _) = true
shouldStay (after _) = true
shouldStay (□ _) = true
shouldStay _ = false

filterTruths : List LTL → List LTL
filterTruths [] = []
filterTruths (ltl ∷ ltls) = if shouldStay ltl then filterTruths ltls else ltl ∷ (filterTruths ltls)

updateTruths : List LTL → List LTL → Truths → Truths
updateTruths add rem tr = truths (add ++ filterTruths (listTruths (rm' rem tr)))

--dum ändring
