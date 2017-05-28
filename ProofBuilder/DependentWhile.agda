module DependentWhile where

open import ELTL
open import SatRel
open import CPL
open import Data.Bool as Bool using (true; false; Bool)
open import Data.Nat
open import Data.Nat

-- This example demonstrates how to prove termination for two co-processes,
-- depending on each other for termination. The proof also shows the need for
-- proving partial termination. If s10 would be changed to "while true", it
-- would no longer be possible to show termination of s9, thus s8 may not
-- terminate.

{- == The program ==

s0: {
  s1: p = true
  s2: q = false
  s3: cobegin
    s4 {
      s5: p = false
      s6: while ∼ q
        s7: x = 5
    }
  ||
    s8: {
      s9: while p
        s10: while false
          s11: x = 6
      s12: q = true
    }
  coend
  s13: x = 1
}
-}

s0  = stm "s0" (block ((((first "s1") :: "s2") :: "s3") :: "s13"))
s1  = stm "s1" ("p" :=b (bool true))
s2  = stm "s2" ("q" :=b (bool false))
s3  = stm "s3" ("s4" || "s8")
s4  = stm "s4" (block ((first "s5") :: "s6"))
s5  = stm "s5" ("p" :=b (bool false))
s6  = stm "s6" (while (~ (var "q")) "s7")
s7  = stm "s7" ("x" :=n (nat 5))
s8  = stm "s8" (block ((first "s9") :: "s12"))
s9  = stm "s9" (while (var "p") "s10")
s10 = stm "s10" (while (bool false) "s11")
s11 = stm "s11" ("x" :=n (nat 6))
s12 = stm "s12" ("q" :=b (bool true))
s13 = stm "s13" ("x" :=n (nat 1))


s0~>s2 : {p : Prog s0 0} → p ⊨ (at "s0" ~> at "s2")
s0~>s2 = ~>-t (enterBlock s0 "s1" (record {})) (~>-t (:=b-T-step s1) (flow s0 (record {})))

s2~>s3 : {p : Prog s0 0} → p ⊨ (at "s2" ~> at "s3")
s2~>s3 = ~>-t (:=b-F-step s2) (flow s0 (record {}))

postulate q=>□q : {p : Prog s0 0} → p ⊨ ((b* (var "q")) ~> □ (b* (var "q")))
postulate ~p=>□~p : {p : Prog s0 0} → p ⊨ ((b* (~ (var "p"))) ~> □ (b* (~ (var "p"))))

s8~>~p : {p : Prog s0 0} → p ⊨ (at "s8" ~> (b* (~ (var "p"))))
s8~>~p = ~>-t (infPar₁ s3) (~>-t (enterBlock s4 "s5" (record {})) (~>-∧-e₂ (:=b-F-R s5)))

s9~>s9' : {p : Prog s0 0} → p ⊨ (at "s9" ~> af "s9")
s9~>s9' = exitWhileT s9 (~>-t (infBlock s8 "s9" (record {})) (~>-t s8~>~p ~p=>□~p)) (~>-t (skipWhile s10) (retWhile s9))

s8~>s12 : {p : Prog s0 0} → p ⊨ (at "s8" ~> at "s12")
s8~>s12 = ~>-t (~>-t (enterBlock s8 "s9" (record {})) s9~>s9') (flow s8 (record {}))

s8~>s8' : {p : Prog s0 0} → p ⊨ (at "s8" ~> af "s8")
s8~>s8' = ~>-t (~>-t s8~>s12 (:=b-T-step s12)) (exitBlock s8 (record {}))

s8~>□q : {p : Prog s0 0} → p ⊨ (at "s8" ~> □ (b* (var "q")))
s8~>□q = ~>-t (~>-t s8~>s12 (~>-∧-e₂ (:=b-T-R s12))) q=>□q

s6~>s6' : {p : Prog s0 0} → p ⊨ (at "s6" ~> af "s6")
s6~>s6' = exitWhileF s6 (~>-t (~>-t (infBlock s4 "s6" (record {})) (infPar₂ s3)) s8~>□q) (~>-t (:=n-step s7) (retWhile s6))

s4~>s6' : {p : Prog s0 0} → p ⊨ (at "s4" ~> af "s6")
s4~>s6' = ~>-t (~>-t (~>-t (enterBlock s4 "s5" (record {})) (:=b-F-step s5)) (flow s4 (record {}))) s6~>s6'

s4~>s4' : {p : Prog s0 0} → p ⊨ (at "s4" ~> af "s4")
s4~>s4' = ~>-t s4~>s6' (exitBlock s4 (record {}))

s3~>s3' : {p : Prog s0 0} → p ⊨ (at "s3" ~> af "s3")
s3~>s3' = ~>-t (~>-t (enterPar s3) (join s3 s4~>s4' s8~>s8')) (exitPar s3)

s3'~>s13 : {p : Prog s0 0} → p ⊨ (af "s3" ~> at "s13")
s3'~>s13 = flow s0 (record {})

s13'~>s0' : {p : Prog s0 0} → p ⊨ (at "s13" ~> af "s0")
s13'~>s0' = ~>-t (:=n-step s13) (exitBlock s0 (record {}))

p⊨term : {p : Prog s0 0} → p ⊨ term
p⊨term = term (~>-t (~>-t s0~>s2 (~>-t (~>-t s2~>s3 s3~>s3') s3'~>s13)) s13'~>s0')
