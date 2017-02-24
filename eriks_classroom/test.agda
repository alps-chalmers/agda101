module test where
open import List
open import Bool
open import N
open import Maybe


data Pair (A B : Set) : Set where
  pair : A -> B -> Pair A B

record Env : Set where
  field x : N
        y : N
        z : N
        p : Bool
        q : Bool

mkEnv : Env
mkEnv = record {x = N0; y = N0; z = N0; p = false; q = false}

data BVar : Set where
  P : BVar
  Q : BVar
data NVar : Set where
  X : NVar
  Y : NVar
  Z : NVar

getNVar : Env -> NVar -> N
getNVar env X = Env.x env
getNVar env Y = Env.y env
getNVar env Z = Env.z env

setNVar : Env -> NVar -> N -> Env
setNVar env X n = record env {x = n}
setNVar env Y n = record env {y = n}
setNVar env Z n = record env {z = n}

-- sets the value of var in second env to value of var i first env
moveNVar : Env -> Env -> NVar -> Env
moveNVar from to var = setNVar to var (getNVar from var)

getBVar : Env -> BVar -> Bool
getBVar env P = Env.p env
getBVar env Q = Env.q env

setBVar : Env -> BVar -> Bool -> Env
setBVar env P n = record env {p = n}
setBVar env Q n = record env {q = n}


-- sets the value of var in second env to value of var i first env
moveBVar : Env -> Env -> BVar -> Env
moveBVar from to var = setBVar to var (getBVar from var)

data NatExpr : Set where
  varN   : NVar -> NatExpr
  coNst : N -> NatExpr
  add   : NatExpr -> NatExpr -> NatExpr

evalNatExpr : Env -> NatExpr -> N
evalNatExpr env (varN n)  = getNVar env n
evalNatExpr env (coNst n) = n
evalNatExpr env (add expr1 expr2)
                          = (evalNatExpr env expr1) + (evalNatExpr env expr2)

data BoolExpr : Set where
  varB   : BVar -> BoolExpr
  constB : Bool -> BoolExpr
  andexpr : BoolExpr -> BoolExpr -> BoolExpr
  orexpr : BoolExpr -> BoolExpr -> BoolExpr
  gt     : NatExpr -> NatExpr -> BoolExpr
  gte    : NatExpr -> NatExpr -> BoolExpr
  lt     : NatExpr -> NatExpr -> BoolExpr
  lte    : NatExpr -> NatExpr -> BoolExpr

evalBoolExpr : Env -> BoolExpr -> Bool
evalBoolExpr env (varB v) = getBVar env v
evalBoolExpr _ (constB b) = b
evalBoolExpr env (andexpr expr1 expr2) = (evalBoolExpr env expr1) and
                                         (evalBoolExpr env expr2)
evalBoolExpr env (orexpr expr1 expr2) = (evalBoolExpr env expr1) or
                                        (evalBoolExpr env expr2)
evalBoolExpr env (gt expr1 expr2) =
                    (evalNatExpr env expr1) > (evalNatExpr env expr2)
evalBoolExpr env (lt expr1 expr2) =
                    (evalNatExpr env expr1) < (evalNatExpr env expr2)
evalBoolExpr env (gte expr1 expr2) =
                    (evalNatExpr env expr1) <= (evalNatExpr env expr2)
evalBoolExpr env (lte expr1 expr2) =
                    (evalNatExpr env expr1) >= (evalNatExpr env expr2)



data VoidExpr : Set where
  loadN     : NVar -> VoidExpr
  storeN    : NVar -> VoidExpr
  assigN    : NVar -> NatExpr -> VoidExpr
  incremeNt : NVar -> VoidExpr
  loadB     : BVar -> VoidExpr
  storeB    : BVar -> VoidExpr
  assignB   : BVar -> BoolExpr -> VoidExpr
  ifelse    : BoolExpr -> VoidExpr -> VoidExpr -> VoidExpr
  nop       : VoidExpr

evalVoidExpr : Env -> Env -> VoidExpr -> Pair Env Env
evalVoidExpr global local (loadN v) = pair global
                                             (moveNVar global local v)
evalVoidExpr global local (storeN v) = pair (moveNVar local global v)
                                              local
evalVoidExpr global local (assigN v expr) = pair global
                                                   (setNVar local v
                                                            (evalNatExpr local
                                                                         expr))
evalVoidExpr global local (incremeNt v) = pair global
                                                 (setNVar local
                                                          v
                                                          (s (getNVar local
                                                                      v)))


evalVoidExpr global local (loadB v) = pair global
                                             (moveBVar global local v)
evalVoidExpr global local (storeB v) = pair (moveBVar local global v)
                                              local
evalVoidExpr global local (assignB v expr) = pair global
                                                   (setBVar local v
                                                            (evalBoolExpr local
                                                                         expr))
evalVoidExpr global local nop = pair global local
evalVoidExpr global local (ifelse cond a b) with (evalBoolExpr local cond)
... | true  = evalVoidExpr global local a
... | false = evalVoidExpr global local b


