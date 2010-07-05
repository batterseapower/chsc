#include "../Prelude.hs"

data Tree a = Leaf a | Branch (Tree a) (Tree a)
