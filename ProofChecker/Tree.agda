module Tree where

open import Nat
open import Lists

{-# BUILTIN NATURAL Nat #-}

data Tree (A : Set) : Set where
  leaf : A → Tree A
  branch : Tree A → List (Tree A) → Tree A

tree0 tree1 tree2 tree : Tree Nat
tree0 = leaf 0
tree1 = branch (leaf 1) ((leaf 2) :: ((leaf 3) :: empty))
tree2 = branch (leaf 4) ((leaf 3) :: empty)
tree = branch tree0 (tree1 :: (tree2 :: empty))
