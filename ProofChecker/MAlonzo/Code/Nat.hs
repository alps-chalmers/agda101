{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Nat where

import MAlonzo.RTE (coe, erased, addInt, subInt, mulInt, quotInt,
                    remInt, geqInt, ltInt, eqInt, eqFloat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Bool

name2 = "Nat.Nat"
d2 = ()
data T2 a0 = C4 | C6 a0
name8 = "Nat._+_"
d8 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = coe subInt v0 (1 :: Integer) in
           coe addInt (1 :: Integer) (coe d8 v2 v1)
name16 = "Nat._-_"
d16 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = coe subInt v0 (1 :: Integer) in
           case coe v1 of
             0 -> coe v0
             _ -> let v3 = coe subInt v1 (1 :: Integer) in coe d16 v2 v3
name26 = "Nat._*_"
d26 v0 v1
  = case coe v0 of
      0 -> 0 :: Integer
      _ -> let v2 = coe subInt v0 (1 :: Integer) in
           coe d8 v1 (coe d26 v2 v1)
name34 = "Nat._<_"
d34 v0 v1
  = case coe v1 of
      0 -> coe MAlonzo.Code.Bool.C6
      _ -> let v2 = coe subInt v1 (1 :: Integer) in
           case coe v0 of
             0 -> coe MAlonzo.Code.Bool.C4
             _ -> let v3 = coe subInt v0 (1 :: Integer) in coe d34 v3 v2
name40 = "Nat._==_"
d40 v0 v1
  = case coe v0 of
      0 -> case coe v1 of
             0 -> coe MAlonzo.Code.Bool.C4
             _ -> coe MAlonzo.Code.Bool.C6
      _ -> let v2 = coe subInt v0 (1 :: Integer) in
           case coe v1 of
             0 -> coe MAlonzo.Code.Bool.C6
             _ -> let v3 = coe subInt v1 (1 :: Integer) in coe d40 v2 v3