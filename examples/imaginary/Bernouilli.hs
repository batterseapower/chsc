import Data.Ratio

#include "../Prelude.hs"

lit0'Rational = 0 :: Rational

rational = (Data.Ratio.%) :: Integer -> Integer -> Rational

show'Rational = show :: Rational -> String

add'Rational = (Prelude.+) :: Rational -> Rational -> Rational
subtract'Rational = (Prelude.-) :: Rational -> Rational -> Rational
