{-# LANGUAGE EmptyDataDecls, ExistentialQuantification,
             ScopedTypeVariables, NoMonomorphismRestriction, Rank2Types #-}
module MAlonzo.Code.Props where

import MAlonzo.RTE (coe, erased, addInt, subInt, mulInt, quotInt,
                    remInt, geqInt, ltInt, eqInt, eqFloat)
import qualified MAlonzo.RTE
import qualified Data.Text

name2 = "Props.Props"
d2 = ()
data T2 a0 a1
  = C4 | C6 | C8 a0 a1 | C10 a0 a1 | C12 a0 a1 | C14 a0 | C16 a0