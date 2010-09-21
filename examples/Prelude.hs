import qualified Prelude
import Prelude hiding ((+), (-), (*), div, mod)

prelude_error = Prelude.error

(+) = (Prelude.+) :: Int -> Int -> Int
(-) = (Prelude.-) :: Int -> Int -> Int
(*) = (Prelude.*) :: Int -> Int -> Int
div = (Prelude.div) :: Int -> Int -> Int
mod = (Prelude.mod) :: Int -> Int -> Int

lit_1'Integer = -1 :: Integer
lit0'Integer = 0 :: Integer
lit1'Integer = 1 :: Integer
lit2'Integer = 2 :: Integer

lit_1'Double = -1 :: Double
lit0'Double = 0 :: Double
lit1'Double = 1 :: Double
lit2'Double = 2 :: Double

show'Int = show :: Int -> String
show'Integer = show :: Integer -> String
show'Double = show :: Double -> String

read'Int = read :: String -> Int
read'Integer = read :: String -> Integer
read'Double = read :: String -> Double

fromIntegral'Int'Integer = Prelude.fromIntegral :: Int -> Integer
fromIntegral'Int'Double = Prelude.fromIntegral :: Int -> Double

ipow'Double'Int = (Prelude.^) :: Double -> Int -> Double

round'Double'Int = Prelude.round :: Double -> Int
ceiling'Double'Int = Prelude.ceiling :: Double -> Int

div'Int = Prelude.div :: Int -> Int -> Int
max'Int = Prelude.max :: Int -> Int -> Int
odd'Int = Prelude.odd :: Int -> Bool

gt'Integer = (Prelude.>) :: Integer -> Integer -> Bool
add'Integer = (Prelude.+) :: Integer -> Integer -> Integer
subtract'Integer = (Prelude.-) :: Integer -> Integer -> Integer
multiply'Integer = (Prelude.*) :: Integer -> Integer -> Integer
div'Integer = (Prelude.div) :: Integer -> Integer -> Integer
negate'Integer = Prelude.negate :: Integer -> Integer

lte'Double = (Prelude.<=) :: Double -> Double -> Bool
add'Double = (Prelude.+) :: Double -> Double -> Double
subtract'Double = (Prelude.-) :: Double -> Double -> Double
multiply'Double = (Prelude.*) :: Double -> Double -> Double
divide'Double = (Prelude./) :: Double -> Double -> Double
negate'Double = Prelude.negate :: Double -> Double

eq'Char = (Prelude.==) :: Char -> Char -> Bool
neq'Char = (Prelude./=) :: Char -> Char -> Bool
lte'Char = (Prelude.<=) :: Char -> Char -> Bool
lt'Char = (Prelude.<) :: Char -> Char -> Bool
gte'Char = (Prelude.>=) :: Char -> Char -> Bool
gt'Char = (Prelude.>) :: Char -> Char -> Bool

succ'Char = Prelude.succ :: Char -> Char
