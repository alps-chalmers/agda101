module test where
open import List
open import Bool
open import N
open import Maybe

record Env : Set where
  field x : N
        y : N
        z : N
        p : Bool
        q : Bool
        w : Bool

newEnv : Env
newEnv = record{ x = zero; y = zero; z = zero; p = false; q = false; w = false}

data Var : Set where
  X : Var
  Y : Var
  Z : Var

data Expr : Set where
  add : Var -> N -> Expr
  addVar : Var -> Var -> Expr

evaladd : Env -> Var -> N -> Env
evaladd env X n = record env {x = ((Env.x env) + n)}
evaladd env Y n = record env {y = ((Env.y env) + n)}
evaladd env Z n = record env {z = ((Env.z env) + n)}

eval : Env -> Expr -> Env
eval env (add v n) = evaladd env v n
eval env (addVar v X) = evaladd env v (Env.x env)
eval env (addVar v Y) = evaladd env v (Env.y env)
eval env (addVar v Z) = evaladd env v (Env.z env)

incremented_x_env = eval newEnv (add X N1)

-- is it true that if we increment 0 its greater than 0? can we prove it?
ultimate_truth : isTrue (Env.x incremented_x_env > zero)
ultimate_truth = record {}

