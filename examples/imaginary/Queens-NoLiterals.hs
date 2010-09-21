#include "../Prelude.hs"

-- Neils hack. See if residualising this portion makes any difference:
safer x d q = x `neq'Int` q && x `neq'Int` q+d && x `neq'Int` q-d

lit0'Int = 0 :: Int
lit1'Int = 1 :: Int

eq'Int = (Prelude.==) :: Int -> Int -> Bool
gt'Int = (Prelude.>) :: Int -> Int -> Bool
add'Int = (Prelude.+) :: Int -> Int -> Int
subtract'Int = (Prelude.-) :: Int -> Int -> Int

