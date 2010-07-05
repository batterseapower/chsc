#include "../Prelude.hs"

data Tree a = Empty | Node (Tree a) a (Tree a)
            deriving (Eq, Show)
