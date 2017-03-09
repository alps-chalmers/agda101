{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.MapFold where

import MAlonzo.RTE (coe, erased, addInt, subInt, mulInt, quotInt,
                    remInt, geqInt, ltInt, eqInt, eqFloat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Bool
import qualified MAlonzo.Code.Lists

name8 = "MapFold.map"
d8 v0 v1 v2 v3 = du8 v2 v3
du8 v0 v1
  = case coe v1 of
      MAlonzo.Code.Lists.C8 -> coe v1
      MAlonzo.Code.Lists.C10 v2 v3
        -> coe MAlonzo.Code.Lists.C10 (coe v0 v2) (coe du8 v0 v3)
      _ -> coe MAlonzo.RTE.mazUnreachableError
name22 = "MapFold.foldl"
d22 v0 v1 v2 v3 v4 = du22 v2 v3 v4
du22 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Lists.C8 -> coe v1
      MAlonzo.Code.Lists.C10 v3 v4 -> coe du22 v0 (coe v0 v1 v3) v4
      _ -> coe MAlonzo.RTE.mazUnreachableError
name40 = "MapFold.filter"
d40 v0 v1 v2 = du40 v1 v2
du40 v0 v1
  = coe
      du22
      (\ v2 v3 ->
         coe
           MAlonzo.Code.Bool.du10 (coe v0 v3)
           (coe MAlonzo.Code.Lists.C10 v3 v2) v2)
      MAlonzo.Code.Lists.C8 v1
name50 = "MapFold.test"
d50
  = coe
      MAlonzo.Code.Lists.C10 MAlonzo.Code.Bool.C6
      (coe
         MAlonzo.Code.Lists.C10 MAlonzo.Code.Bool.C4
         (coe
            MAlonzo.Code.Lists.C10 MAlonzo.Code.Bool.C6 MAlonzo.Code.Lists.C8))
name52 = "MapFold.run"
d52 = coe du40 (\ v0 -> v0) d50