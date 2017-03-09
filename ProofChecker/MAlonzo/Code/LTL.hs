{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.LTL where

import MAlonzo.RTE (coe, erased, addInt, subInt, mulInt, quotInt,
                    remInt, geqInt, ltInt, eqInt, eqFloat)
import qualified MAlonzo.RTE
import qualified Data.Text

name4 = "LTL._\8801_"
d4 a0 a1 a2 = ()
newtype T4 a0 = C10 a0
name12 = "LTL.LTL"
d12 = ()
data T12 a0 a1
  = C14 | C16 | C18 a0 | C20 a0 | C22 a0 | C24 a0 a1 | C26 a0 a1 |
    C28 a0 a1 | C30 a0 a1 | C32 a0 | C34 a0 | C36 a0 a1