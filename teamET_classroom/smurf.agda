module smurf where

-------------------------------------------------
data Nat : Set where
  zero : Nat
  suc : Nat -> Nat

data Fin : Nat -> Set where
  fzero : {n : Nat} -> Fin (suc n)
  fsuc  : {n : Nat} -> (i : Fin n) -> Fin (suc n)

--------------------------------------------------

data Prop : Set where
  floor roof   : Prop
  patom        : {n : Nat} -> Fin n -> Prop
  ~_           : Prop -> Prop
  _and_ _or_ _=>_ : Prop -> Prop -> Prop

data Context : Nat -> Set where
  void : Context zero
  _*_  : {n : Nat} -> Context n -> Prop -> Context (suc n) 

--gargamel : Context (suc zero)
--gargamel = void * (patom fzero and patom (fsuc fzero))

data _sneT_ : {n : Nat} -> (Gamma : Context n) -> (psi : Prop) -> Set where
  var     : {n : Nat} -> {Gamma : Context n} -> {psi : Prop}                             -> (Gamma * psi) sneT psi
  weaken  : {n : Nat} -> {Gamma : Context n} -> {psi phi : Prop} -> Gamma sneT psi       -> (Gamma * phi) sneT psi
  roof-i  : {n : Nat} -> {Gamma : Context n}                                             -> Gamma sneT roof
  floor-i : {n : Nat} -> {Gamma : Context n} -> {psi : Prop} -> Gamma sneT floor         -> Gamma sneT psi                                  
  ~-i     : {n : Nat} -> {Gamma : Context n} -> {psi : Prop} -> (Gamma * psi) sneT floor -> Gamma sneT (~ psi)
