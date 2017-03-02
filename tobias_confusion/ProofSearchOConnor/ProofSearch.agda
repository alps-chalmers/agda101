module ProofSearch where

{--
-- Props from other document on prop. logic
data Props : Set where
   ⊤ ⊥          : Props
   ¬_           : Props -> Props
-------------------------------------------
--}

data Dec (P : Set) : Set where
  yes : P  -> Dec P
  no  : ¬ P -> Dec P
