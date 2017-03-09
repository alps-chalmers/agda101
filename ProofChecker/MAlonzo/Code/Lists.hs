{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Lists where

import MAlonzo.RTE (coe, erased, addInt, subInt, mulInt, quotInt,
                    remInt, geqInt, ltInt, eqInt, eqFloat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Bool
import qualified MAlonzo.Code.Maybe
import qualified MAlonzo.Code.Nat

name4 = "Lists.List"
d4 a0 = ()
data T4 a0 a1 = C8 | C10 a0 a1
name14 = "Lists.Eq"
d14 a0 = ()
data T14 a0 a1 = C18 a0 a1 | C20 a0 a1
name24 = "Lists.isEmpty"
d24 v0 v1 = du24 v1
du24 v0
  = case coe v0 of
      C8 -> coe MAlonzo.Code.Bool.C4
      C10 v1 v2 -> coe MAlonzo.Code.Bool.C6
      _ -> coe MAlonzo.RTE.mazUnreachableError
name32 = "Lists.add"
d32 v0 v1 v2 = du32 v1 v2
du32 v0 v1 = coe C10 v0 v1
name40 = "Lists.head"
d40 v0 v1 = du40 v1
du40 v0
  = case coe v0 of
      C8 -> coe MAlonzo.Code.Maybe.C8
      C10 v1 v2 -> coe MAlonzo.Code.Maybe.C10 v1
      _ -> coe MAlonzo.RTE.mazUnreachableError
name48 = "Lists.tail"
d48 v0 v1 = du48 v1
du48 v0
  = case coe v0 of
      C8 -> coe MAlonzo.Code.Maybe.C8
      C10 v1 v2
        -> let v3 = coe du48 v2 in
           case coe v2 of
             C8 -> coe MAlonzo.Code.Maybe.C10 v1
             _ -> coe v3
      _ -> coe MAlonzo.RTE.mazUnreachableError
name58 = "Lists._++_"
d58 v0 v1 v2 = du58 v1 v2
du58 v0 v1
  = case coe v0 of
      C8 -> coe v1
      C10 v2 v3 -> coe C10 v2 (coe du58 v3 v1)
      _ -> coe MAlonzo.RTE.mazUnreachableError
name72 = "Lists._eq_"
d72 v0 v1 v2 = du72
du72 = MAlonzo.Code.Bool.C4
name80 = "Lists.elem"
d80 v0 v1 v2 v3 = du80 v1 v2 v3
du80 v0 v1 v2
  = case coe v1 of
      C8 -> coe MAlonzo.Code.Bool.C6
      C10 v3 v4
        -> coe
             MAlonzo.Code.Bool.du10 (coe v2 v0 v3) MAlonzo.Code.Bool.C4
             (coe du80 v0 v4 v2)
      _ -> coe MAlonzo.RTE.mazUnreachableError
name92 = "Lists.conc"
d92 v0 v1 = du92 v1
du92 v0
  = case coe v0 of
      C8 -> coe v0
      C10 v1 v2
        -> case coe v1 of
             C8 -> coe du92 v2
             C10 v3 v4 -> coe C10 v3 (coe du92 (coe C10 v4 v2))
             _ -> coe MAlonzo.RTE.mazUnreachableError
      _ -> coe MAlonzo.RTE.mazUnreachableError
name104 = "Lists.IList"
d104 a0 a1 = ()
data T104 a0 a1 a2 = C108 | C112 a0 a1 a2
name118 = "Lists.headI"
d118 v0 v1 v2 = du118 v2
du118 v0
  = case coe v0 of
      C112 v1 v2 v3 -> coe v2
      _ -> coe MAlonzo.RTE.mazUnreachableError
name130 = "Lists._+++_"
d130 v0 v1 v2 v3 v4 = du130 v2 v3 v4
du130 v0 v1 v2
  = case coe v1 of
      C108 -> coe v2
      C112 v3 v4 v5
        -> coe C112 (coe MAlonzo.Code.Nat.d8 v3 v0) v4 (coe du130 v0 v5 v2)
      _ -> coe MAlonzo.RTE.mazUnreachableError
name144 = "Lists.length"
d144 v0 v1 v2 = du144 v1
du144 v0 = coe v0