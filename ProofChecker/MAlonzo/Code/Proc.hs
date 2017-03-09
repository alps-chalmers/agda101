{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Proc where

import MAlonzo.RTE (coe, erased, addInt, subInt, mulInt, quotInt,
                    remInt, geqInt, ltInt, eqInt, eqFloat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Lists
import qualified MAlonzo.Code.MapFold

name2 = "Proc.Stm"
d2 = ()
data T2 a0 = C4 | C6 | C8 a0
name14 = "Proc.Hoare"
d14 a0 a1 = ()
data T14 a0 a1 a2 = C32 a0 a1 a2
name26 = "Proc.Hoare.pre"
d26 v0
  = case coe v0 of
      C32 v1 v2 v3 -> coe v1
      _ -> coe MAlonzo.RTE.mazUnreachableError
name28 = "Proc.Hoare.action"
d28 v0
  = case coe v0 of
      C32 v1 v2 v3 -> coe v2
      _ -> coe MAlonzo.RTE.mazUnreachableError
name30 = "Proc.Hoare.post"
d30 v0
  = case coe v0 of
      C32 v1 v2 v3 -> coe v3
      _ -> coe MAlonzo.RTE.mazUnreachableError
name34 = "Proc.Proc"
d34 = ()
newtype T34 a0 = C36 a0
name42 = "Proc.chain"
d42 v0 v1
  = coe
      C32 (coe d26 v1)
      (coe MAlonzo.Code.Lists.C10 (coe d28 v0) (coe d28 v1)) (coe d30 v0)
name52 = "Proc.chainProc"
d52 v0 v1 v2 = du52 v2
du52 v0
  = case coe v0 of
      C36 v1
        -> case coe v1 of
             MAlonzo.Code.Lists.C8 -> coe C32 v1 v1 v1
             MAlonzo.Code.Lists.C10 v2 v3
               -> coe
                    MAlonzo.Code.MapFold.du22
                    (\ v4 v5 ->
                       coe
                         C32 (coe d26 v4)
                         (coe MAlonzo.Code.Lists.C10 (coe d28 v5) (coe d28 v4))
                         (coe d30 v5))
                    (coe
                       C32 (coe d26 v2)
                       (coe MAlonzo.Code.Lists.C10 (coe d28 v2) MAlonzo.Code.Lists.C8)
                       (coe d30 v2))
                    v3
             _ -> coe MAlonzo.RTE.mazUnreachableError
      _ -> coe MAlonzo.RTE.mazUnreachableError