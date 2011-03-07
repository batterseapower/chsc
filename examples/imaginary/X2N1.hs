import Data.Complex

#include "../Prelude.hs"

f :: Int -> Complex Double
f n = mkPolar 1 ((2 Prelude.* Prelude.pi) / Prelude.fromIntegral n) Prelude.^ n

realPart'Double = realPart :: Complex Double -> Double
add'ComplexDouble = (Prelude.+) :: Complex Double -> Complex Double -> Complex Double
lit0'ComplexDouble = 0 :: Complex Double
