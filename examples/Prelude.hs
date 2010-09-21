import qualified Prelude
--import Prelude hiding ((+), (-), (*), div, mod)
import Prelude (Int, Char, Bool(..), Maybe(..), Either(..), seq)

prelude_error = Prelude.error

lit_1'Integer = -1 :: Prelude.Integer
lit0'Integer = 0 :: Prelude.Integer
lit1'Integer = 1 :: Prelude.Integer
lit2'Integer = 2 :: Prelude.Integer

lit_1'Double = -1 :: Prelude.Double
lit0'Double = 0 :: Prelude.Double
lit1'Double = 1 :: Prelude.Double
lit2'Double = 2 :: Prelude.Double

show'Int = Prelude.show :: Int -> Prelude.String
show'Integer = Prelude.show :: Prelude.Integer -> Prelude.String
show'Double = Prelude.show :: Prelude.Double -> Prelude.String

read'Int = Prelude.read :: Prelude.String -> Int
read'Integer = Prelude.read :: Prelude.String -> Prelude.Integer
read'Double = Prelude.read :: Prelude.String -> Prelude.Double

fromIntegral'Int'Integer = Prelude.fromIntegral :: Int -> Prelude.Integer
fromIntegral'Int'Double = Prelude.fromIntegral :: Int -> Prelude.Double

ipow'Double'Int = (Prelude.^) :: Prelude.Double -> Int -> Prelude.Double

round'Double'Int = Prelude.round :: Prelude.Double -> Int
ceiling'Double'Int = Prelude.ceiling :: Prelude.Double -> Int

eq'Int = (Prelude.==) :: Int -> Int -> Bool
neq'Int = (Prelude./=) :: Int -> Int -> Bool
gt'Int = (Prelude.>) :: Int -> Int -> Bool
gte'Int = (Prelude.>=) :: Int -> Int -> Bool
lt'Int = (Prelude.<) :: Int -> Int -> Bool
lte'Int = (Prelude.<=) :: Int -> Int -> Bool
add'Int = (Prelude.+) :: Int -> Int -> Int
subtract'Int = (Prelude.-) :: Int -> Int -> Int
multiply'Int = (Prelude.*) :: Int -> Int -> Int
div'Int = Prelude.div :: Int -> Int -> Int
mod'Int = Prelude.mod :: Int -> Int -> Int
max'Int = Prelude.max :: Int -> Int -> Int

gt'Integer = (Prelude.>) :: Prelude.Integer -> Prelude.Integer -> Bool
add'Integer = (Prelude.+) :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
subtract'Integer = (Prelude.-) :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
multiply'Integer = (Prelude.*) :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
div'Integer = Prelude.div :: Prelude.Integer -> Prelude.Integer -> Prelude.Integer
negate'Integer = Prelude.negate :: Prelude.Integer -> Prelude.Integer

lte'Double = (Prelude.<=) :: Prelude.Double -> Prelude.Double -> Bool
add'Double = (Prelude.+) :: Prelude.Double -> Prelude.Double -> Prelude.Double
subtract'Double = (Prelude.-) :: Prelude.Double -> Prelude.Double -> Prelude.Double
multiply'Double = (Prelude.*) :: Prelude.Double -> Prelude.Double -> Prelude.Double
divide'Double = (Prelude./) :: Prelude.Double -> Prelude.Double -> Prelude.Double
negate'Double = Prelude.negate :: Prelude.Double -> Prelude.Double

eq'Char = (Prelude.==) :: Char -> Char -> Bool
neq'Char = (Prelude./=) :: Char -> Char -> Bool
lte'Char = (Prelude.<=) :: Char -> Char -> Bool
lt'Char = (Prelude.<) :: Char -> Char -> Bool
gte'Char = (Prelude.>=) :: Char -> Char -> Bool
gt'Char = (Prelude.>) :: Char -> Char -> Bool

succ'Char = Prelude.succ :: Char -> Char
