{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Bool where

import MAlonzo.RTE (coe, erased, addInt, subInt, mulInt, quotInt,
                    remInt, geqInt, ltInt, eqInt, eqFloat)
import qualified MAlonzo.RTE
import qualified Data.Text

name2 = "Bool.Bool"
d2 = ()
data T2 = C4 | C6
name10 = "Bool.if_then_else_"
d10 v0 v1 v2 v3 = du10 v1 v2 v3
du10 v0 v1 v2
  = case coe v0 of
      C4 -> coe v1
      C6 -> coe v2
      _ -> coe MAlonzo.RTE.mazUnreachableError
name20 = "Bool._&&_"
d20 v0 v1
  = case coe v0 of
      C4
        -> case coe v1 of
             C4 -> coe v1
             _ -> coe C6
      _ -> coe C6
name22 = "Bool._||_"
d22 v0 v1
  = case coe v0 of
      C6
        -> case coe v1 of
             C6 -> coe v1
             _ -> coe C4
      _ -> coe C4
name24 = "Bool.not"
d24 v0
  = case coe v0 of
      C4 -> coe C6
      C6 -> coe C4
      _ -> coe MAlonzo.RTE.mazUnreachableError