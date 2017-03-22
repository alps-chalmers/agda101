module MapFold where

open import Lists
open import Bool

map : {A B : Set} -> (f : (A -> B)) -> List A -> List B
map _ [] = []
map f (x :: xs) = (f x) :: (map f xs)

foldl : {A B : Set} -> (f : (A -> B -> A)) -> A -> List B -> A
foldl f a [] = a
foldl f a (x :: xs) = foldl f (f a x) xs

filter : {A : Set} -> (f : A -> Bool) -> List A -> List A
filter f xs = foldl (λ ls x → if (f x) then x :: ls else ls) [] xs

test : List Bool
test = false :: (true :: (false :: []))

run = filter (λ x -> x) test
