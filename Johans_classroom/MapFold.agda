module MapFold where

open import Lists

map : {A B : Set} -> (f : (A -> B)) -> List A -> List B
map _ [] = []
map f (x :: xs) = (f x) :: (map f xs)

foldl : {A B : Set} -> (f : (A -> B -> A)) -> A -> List B -> A
foldl f a [] = a
foldl f a (x :: xs) = foldl f (f a x) xs
