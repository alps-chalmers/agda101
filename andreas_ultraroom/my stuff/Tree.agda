module Tree where

open import Data.Nat
open import Lists

data Tree (A : Set) : Set where
 leaf : A → Tree A
 branch : Tree A → List (Tree A) → Tree A

{-
tree0 tree1 tree2 tree : Tree ℕ
tree0 = leaf 0
tree1 = branch (leaf 1) (leaf 2) (leaf 3)
tree2 = leaf 4
tree  = branch tree0 tree1 tree2
-}
t0 t1 t2 t : Tree ℕ
t0 = leaf 0
t1 = branch (leaf 1) ((leaf 2) :: ((leaf 3) :: empty))
t2 = branch (leaf 4) ((leaf 3) :: empty)
t = branch t0 (t1 :: (t2 :: empty))
