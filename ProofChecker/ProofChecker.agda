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
open import Program
open import LTL
open import Translator
open import Label
open import Rules
open import Function
open import Data.String as String renaming (_++_ to _s++_)
open import LTLRule
open import Truths
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

{-
  Checks if a program rule is applied in a legal way
  legalApplication : program translation → true LTL formulae → rule to apply on the
  LTL formula → valid proof
-}
legalApplication : {φ : LTL} {a : Action} → List TransRel → Truths → ProgRule φ a → ValidProof
legalApplication {φ} {a} [] tr pr = no ((pLTL φ) s++ " not found when applying " s++ (pRule (progR pr)) s++ " to " s++ (pTruths tr))
  -- If passed an empty program, return that it's invalid with an error message
legalApplication {φ} {a} (< pre > a' < post > ∷ rels) tr pr = if isIn pre tr ∧ (isEqA a a' ∧ isEq φ pre) then yes (updateTruths (post ∷ []) (pre ∷ []) tr) else legalApplication rels tr pr
  -- If a triple (see Translator) is in the translation, its precondition is
  -- identical to a true LTL formula and its action is identical to the rule's
  -- action, return that it's a valid proof for the postcondition. Else continue

{-
  Checks if an LTL-rule is applied in a legal way
  applyLTL-R : true LTL formulae → LTL rule → valid proof
-}
applyLTL-R : Truths → LTLRule → ValidProof
applyLTL-R tr (∧-e₁ (φ ∧' ψ)) = if (isIn (φ ∧' ψ) tr) then (yes (updateTruths (φ ∷ []) [] (rm (φ ∧' ψ) tr))) else (no ((pLTL (φ ∧' ψ)) s++ " is not in " s++ (pTruths tr)))
  -- and elimination (see LTLRules)
applyLTL-R tr (∧-e₂ (φ ∧' ψ)) = if (isIn (φ ∧' ψ) tr) then (yes (updateTruths (ψ ∷ []) [] (rm (φ ∧' ψ) tr))) else (no ((pLTL (φ ∧' ψ)) s++ " is not in " s++ (pTruths tr)))
  -- and elimination (see LTLRules)
applyLTL-R tr (∨-i₁ ψ φ) = if (isIn φ tr) then (yes (updateTruths ((ψ ∨' φ) ∷ []) [] (rm φ tr))) else (no ((pLTL φ) s++ " is not in " s++ (pTruths tr)))
  -- or insertion (see LTLRules)
applyLTL-R tr (∨-i₂ ψ φ) = if (isIn φ tr) then (yes (updateTruths ((φ ∨' ψ) ∷ []) [] (rm φ tr))) else (no ((pLTL φ) s++ " is not in " s++ (pTruths tr)))
  -- or insertion (see LTLRules)
applyLTL-R tr (exp-∧ (φ ∧' ψ)) = if (isIn (φ ∧' ψ) tr) then yes (updateTruths (φ ∷ ψ ∷ []) [] tr) else (no ((pLTL (φ ∧' ψ)) s++ " is not in " s++ (pTruths tr)))
applyLTL-R tr (□-e (□ φ)) = if (isIn (□ φ) tr) then yes (updateTruths (φ ∷ []) [] tr) else (no ((pLTL (□ φ)) s++ " is not in " s++ (pTruths tr)))
-- applyLTL-R tr (∨-e (φ ∨' ψ)) = if (isIn (φ ∨' ψ) tr) then yes (updateTruths (φ ∷ ψ ∷ []) [] tr) else (no ((pLTL (φ ∨' ψ)) s++ " is not in " s++ (pTruths tr)))
applyLTL-R tr (∧-i φ ψ) = if ((isIn φ tr) ∧ isIn ψ tr) then yes (updateTruths ((φ ∧' ψ) ∷ []) [] (rm' (φ ∷ (ψ ∷ [])) tr)) else no ((pLTL φ) s++ " or " s++ (pLTL ψ) s++ " are not in " s++ (pTruths tr))
applyLTL-R tr (□-∧-e₁ (□ (φ ∧' ψ))) = if isIn (□ (φ ∧' ψ)) tr then yes (updateTruths ((□ φ) ∷ []) [] tr) else no ((pLTL (□ (φ ∧' ψ))) s++ (" is not in " s++ (pTruths tr)))
applyLTL-R tr (□-∧-e₂ (□ (φ ∧' ψ))) = if isIn (□ (φ ∧' ψ)) tr then yes (updateTruths ((□ ψ) ∷ []) [] tr) else no ((pLTL (□ (φ ∧' ψ))) s++ (" is not in " s++ (pTruths tr)))
applyLTL-R tr r = no ((pRule (ltlR r)) s++ " cannot be applied to " s++ (pTruths tr))
  -- anything else is invalid with a message

{-
  General application function. Takes a translated program, a Thruths and a
  rule. Returns if it is a Valid proof
-}
applyRule : List TransRel → Truths → Rule → ValidProof
applyRule ts tr (progR x) = legalApplication ts tr x
  -- If the passed rule is a program rule, pass on to legalApplication and
  -- return the result
applyRule ts tr (ltlR r) = applyLTL-R tr r
  -- If the passed rule is an LTL rule, pass on to applyLTL-R and rreturn the
  -- result
applyRule ts tr (customR n pre post) = if (isIn pre tr) then (yes (updateTruths (post ∷ []) [] (rm pre tr))) else no err
  where err = "The custom rule " s++ (pRule (customR n pre post)) s++ " cannot be applied to" s++ (pTruths tr)
  -- If the passed rule is a custom rule and if the precondition of the rule and
  -- a true LTL are identical, return that it's valid, else that it's invalid

{-***************-}
{-# TERMINATING #-} -- Used to guarantee that no infinite loop will occur next
{-***************-}

{-
  takeStep tries to apply the rule for a step in the proof.
  takeStep : Program translation → Proof step → Current truths → Resulting LTL
-}
takeStep : List TransRel → ProofStep → ValidProof → ValidProof
takeStep _ _ (no err) = no err
  -- If something invalid is passed (see ValidProof), return the ValidProof
  -- 'no' with error message 'err' (see ValidProof)
takeStep prg (pStep r) (yes tr) = applyRule prg tr r
  -- If a regular proofstep is passed with a valid LTL formulae, pass
  -- information to applyRule (see Rules) and returns the result

  -- if x can be applied, split ∨ and go
takeStep prg (branch (ltlR (∨-e (φ ∨' ψ))) b₁ b₂) (yes tr) = case isIn (φ ∨' ψ) tr of λ
    { true → case res1 of λ -- Return depends on res1 and res2
      { (yes ψ₁) → case res2 of λ  -- First branch is valid, check result of second
        { (yes ψ₂) → if ψ₁ areIn ψ₂ then yes ψ₁ else no ("Mismatch of conclusions " s++ (pTruths ψ₁) s++ " and " s++ (pTruths ψ₂))
          -- If second branch is valid as well, check if they have the same
          -- conclusion
        ; err → err  -- Second branch invalid, return error message 'err'
        }
      ; err  → err   -- First branch invalid, return error message 'err'
      }
    ; _ → no (pLTL (φ ∨' ψ) s++ " cannot be found in truths.")
    }
    where
      res1 = foldl (λ Γ step → takeStep prg step Γ) (yes (updateTruths (φ ∷ []) [] tr)) b₁
        -- Accumulates the result of takeStep on the first branch
      res2 = foldl (λ Γ step → takeStep prg step Γ) (yes (updateTruths (ψ ∷ []) [] tr)) b₂
        -- Accumulates the result of takeStep on the second branch
takeStep _ _ _ = no "Branching can only be used on ∨-formulae. "


{-
  Checks whether a given proof holds for a given program.
  proofCheck : program translation → proof → goal → truths → Resulting Boolean
-}
proofCheck' : List TransRel → Proof → LTL → Truths → ValidProof
proofCheck' _ _ T' _ = yes (truths (T' ∷ []))
  -- If passed something true, return that it is valid because it's true
proofCheck' _ _ ⊥ _ = no  "⊥ always false."
  -- If passed something false, return that it is invalid because it's false
proofCheck' rels pr (□ φ) tr = no "TODO □"
  -- Currently not implemented
  -- TODO add box, maybe prove termination and still holds?
proofCheck' rels pr (φ ⇒ ψ) _ = proofCheck' rels pr ψ (truths (φ ∷ []))
  -- If passed an implication, replace what is known with LHS of implication and
  -- pass on to itself
proofCheck' rels (proof stps) (◇ φ) tr = case res of λ
  -- If passed an eventually proof, return depends on res
  { (yes ψ) → if isIn φ ψ then yes (truths ((◇ φ) ∷ [])) else no ("Wrong conclusion, " s++ (pLTL φ) s++ " is not the same as " s++ (pTruths ψ) s++ ".")
    -- If the proof is valid and concludes the goal, return that it is valid,
    -- else return that it is invalid with an error message
  ; err → err
    -- If the proof is invalid, return that it is invalid with an error message
  }
  where res = foldl (λ t stp → takeStep rels stp t) (yes tr) stps
    -- res accumulates the result of takeStep on the proof passed
proofCheck' rels _ φ tr = if (isIn φ tr) then yes (truths (φ ∷ [])) else no ((pLTL φ) s++ " is not true in the initial state.")
  -- If the goal and what is known if identical, return that it is valid, else
  -- return an error message

{-
  takes a program, custom rules, a proof, a goal and a truths. Returns wether or
  not the proof is valid given the rest of the passed input
-}
proofCheck : Prog → List TransRel → Proof → LTL → Truths → ValidProof
proofCheck pr rels prf g tr = proofCheck' ((translate pr) List.++ rels) prf g tr
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

{-********** Safety Attempt **********-}

_eq_ : ℕ → ℕ → Bool
zero eq zero = true
zero eq suc y = false
suc x eq zero = false
suc x eq suc y = x eq y

_isLarger_ : ℕ → ℕ → Bool
zero isLarger zero = false
zero isLarger suc y = false
suc x isLarger zero = true
suc x isLarger suc y = x isLarger y

_isIn'_ : Label → List Seg → Bool
s x isIn' [] = false
s x isIn' (seg (s x₁) x₂ ∷ segs) = if (x eq x₁) then true else ((s x) isIn' segs)
s x isIn' (block (s x₁) x₂ ∷ segs) = if (x eq x₁) then true else (if ((s x) isIn' x₂) then true else ((s x) isIn' segs))
s x isIn' (par (s x₁) x₂ ∷ segs) = if (x eq x₁) then true else (if ((s x) isIn' x₂) then true else ((s x) isIn' segs))
s x isIn' (while (s x₁) x₂ x₃ ∷ segs) = if (x eq x₁) then true else (if ((s x) isIn' (x₃ ∷ [])) then true else ((s x) isIn' segs))
s x isIn' (if (s x₁) x₂ x₃ ∷ segs) = if (x eq x₁) then true else (if ((s x) isIn' (x₃ ∷ [])) then true else ((s x) isIn' segs))

inPar : Label → List Seg → Bool
inPar _ [] = false
inPar (s x) (seg (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else inPar (s x) segs
inPar (s x) (block (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else (if (inPar (s x) x₂) then true else (inPar (s x) segs))
inPar (s x) (par (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else (if s x isIn' x₂ then true else (inPar (s x) segs))
inPar (s x) (while (s x₁) x₂ sg ∷ segs) = if (x eq x₁) then false else (if (inPar (s x) (sg ∷ [])) then true else (inPar (s x) segs))
inPar (s x) (if (s x₁) x₂ sg ∷ segs) = if (x eq x₁) then false else (if (inPar (s x) (sg ∷ [])) then true else (inPar (s x) segs))

inParLabel : Label → List Seg → Label
inParLabel (s x) [] = s 0
inParLabel (s x) (seg x₁ x₂ ∷ segs) = inParLabel (s x) segs
inParLabel (s x) (block x₁ x₂ ∷ segs) = if ((s x) isIn' x₂) then (inParLabel (s x) x₂) else (inParLabel (s x) segs)
inParLabel (s x) (par x₁ x₂ ∷ segs) = if ((s x) isIn' x₂) then x₁ else (inParLabel (s x) segs)
inParLabel (s x) (while x₁ x₂ x₃ ∷ segs) = if ((s x) isIn' (x₃ ∷ [])) then (inParLabel (s x) (x₃ ∷ [])) else (inParLabel (s x) segs)
inParLabel (s x) (if x₁ x₂ x₃ ∷ segs) = if ((s x) isIn' (x₃ ∷ [])) then (inParLabel (s x) (x₃ ∷ [])) else (inParLabel (s x) segs)

inWhile : Label → List Seg → Bool
inWhile _ [] = false
inWhile (s x) (seg (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else inWhile (s x) segs
inWhile (s x) (block (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else (if (inWhile (s x) x₂) then true else (inWhile (s x) segs))
inWhile (s x) (par (s x₁) x₂ ∷ segs) = if (x eq x₁) then false else (if (inWhile (s x) x₂) then true else (inWhile (s x) segs))
inWhile (s x) (while (s x₁) x₂ sg ∷ segs) = if (x eq x₁) then false else (if ((s x) isIn' (sg ∷ [])) then true else (inWhile (s x) segs))
inWhile (s x) (if (s x₁) x₂ sg ∷ segs) = if (x eq x₁) then false else (if (inWhile (s x) (sg ∷ [])) then true else (inWhile (s x) segs))

inWhileLabel : Label → List Seg → Label
inWhileLabel (s x) [] = s 0
inWhileLabel (s x) (seg x₁ x₂ ∷ segs) = inWhileLabel (s x) segs
inWhileLabel (s x) (block x₁ x₂ ∷ segs) = if ((s x) isIn' x₂) then (inWhileLabel (s x) x₂) else (inWhileLabel (s x) segs)
inWhileLabel (s x) (par x₁ x₂ ∷ segs) = if ((s x) isIn' x₂) then (inWhileLabel (s x) x₂) else (inWhileLabel (s x) segs)
inWhileLabel (s x) (while x₁ x₂ x₃ ∷ segs) = if ((s x) isIn' (x₃ ∷ [])) then x₁ else (inWhileLabel (s x) segs)
inWhileLabel (s x) (if x₁ x₂ x₃ ∷ segs) = if ((s x) isIn' (x₃ ∷ [])) then (inWhileLabel (s x) (x₃ ∷ [])) else (inWhileLabel (s x) segs)

_breaks_ : TransRel → LTL → Bool
< pre > assign < (after (s x)) ∧' (isTrue (vB x₁)) > breaks (∼ (isTrue (vB x₂))) = x₁ == x₂
< pre > assign < (after (s x)) ∧' ((vN x₁) ==n n₁) > breaks ((vN x₂) ==n n₂) = (x₁ == x₂) ∧ not (n₁ eq n₂)
--< pre > assign < after (s x) ∧' (vB x₁ ==b n₁) > breaks (vB x₂ ==b y) = (x₁ == x₂) ∧ ({!!} ∧ {!!})
< pre > assign < (after (s x)) ∧' (∼ (isTrue (vB x₁))) > breaks (isTrue (vB x₂)) = x₁ == x₂
< pre > assign < post > breaks _  = false
< pre > _ < post > breaks _  = false

isAfter : TransRel → Label → Bool
isAfter < at (s x) > assign < post > (s x₁) = x isLarger x₁
isAfter _ _ = false


checkFrom : Label → LTL → List TransRel → Bool
checkFrom (s x) _ [] = true
checkFrom (s x) (∼ (isTrue (vB x₁))) (x₂ ∷ rels) = if (x₂ breaks (∼ (isTrue (vB x₁)))) ∧ (isAfter x₂ (s x)) then false else checkFrom (s x) (∼ (isTrue (vB x₁))) rels
checkFrom (s x) (x₁ ==n n) (x₂ ∷ rels) = if (x₂ breaks (x₁ ==n n)) ∧ (isAfter x₂ (s x)) then false else checkFrom (s x) (x₁ ==n n) rels
--checkFrom (s x) (x₁ ==b y) rels = {!!}
checkFrom (s x) (isTrue (vB x₁)) (x₂ ∷ rels) = if ((x₂ breaks isTrue (vB x₁)) ∧ isAfter x₂ (s x)) then false else checkFrom (s x) (isTrue (vB x₁)) rels
checkFrom _ _ _ = false

_=>_,_ : LTL → LTL → Prog → Bool
after l => □ (∼ (isTrue (vB x))) , prog main = if (inPar l (main ∷ [])) then (if (inWhile l (main ∷ [])) then (checkFrom (inParLabel l (main ∷ [])) (∼ (isTrue (vB x))) (translate (prog main))) ∧ (checkFrom (inWhileLabel l (main ∷ [])) (∼ (isTrue (vB x))) (translate (prog main))) else checkFrom (inParLabel l (main ∷ [])) (∼ (isTrue (vB x))) (translate (prog main))) else (if (inWhile l (main ∷ [])) then (checkFrom (inWhileLabel l (main ∷ [])) (∼ (isTrue (vB x))) (translate (prog main))) else (checkFrom l (∼ (isTrue (vB x))) (translate (prog main))))
after l => □ (x ==n n) , prog main = if (inPar l (main ∷ [])) then (if (inWhile l (main ∷ [])) then (checkFrom (inParLabel l (main ∷ [])) (x ==n n) (translate (prog main))) ∧ (checkFrom (inWhileLabel l (main ∷ [])) (x ==n n) (translate (prog main))) else checkFrom (inParLabel l (main ∷ [])) (x ==n n) (translate (prog main))) else (if (inWhile l (main ∷ [])) then (checkFrom (inWhileLabel l (main ∷ [])) (x ==n n) (translate (prog main))) else (checkFrom l (x ==n n) (translate (prog main))))
--after l => □ (x ==b y) , prg = {!!}
after l => □ (isTrue (vB x)) , prog main = if (inPar l (main ∷ [])) then (if (inWhile l (main ∷ [])) then (checkFrom (inParLabel l (main ∷ [])) (isTrue (vB x)) (translate (prog main))) ∧ (checkFrom (inWhileLabel l (main ∷ [])) (isTrue (vB x)) (translate (prog main))) else checkFrom (inParLabel l (main ∷ [])) (isTrue (vB x)) (translate (prog main))) else (if (inWhile l (main ∷ [])) then (checkFrom (inWhileLabel l (main ∷ [])) (isTrue (vB x)) (translate (prog main))) else (checkFrom l (isTrue (vB x)) (translate (prog main))))
_ => _ , _ = false

