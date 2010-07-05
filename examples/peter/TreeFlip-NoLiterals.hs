#include "../Prelude.hs"

data Tree a = Leaf a | Branch (Tree a) (Tree a)

eq'Int = (==) :: Int -> Int -> Bool
plus'Int = (+) :: Int -> Int -> Int
subtract'Int = (-) :: Int -> Int -> Int
multiply'Int = (*) :: Int -> Int -> Int
