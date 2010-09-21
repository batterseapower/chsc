#include "../Prelude.hs"

data Tree a = Leaf a | Branch (Tree a) (Tree a)

opaque'eq'Int = (Prelude.==) :: Int -> Int -> Bool
opaque'add'Int = (Prelude.+) :: Int -> Int -> Int
opaque'subtract'Int = (Prelude.-) :: Int -> Int -> Int
opaque'multiply'Int = (Prelude.*) :: Int -> Int -> Int
