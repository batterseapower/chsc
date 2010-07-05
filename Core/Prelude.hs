module Core.Prelude where

import Core.Syntax

import Utilities


lam :: Var -> Term -> Term
lam = lambda

int :: Integer -> Term
int = literal . Int

char :: Char -> Term
char = literal . Char


add :: Term -> Term -> Term
add e1 e2 = primOp Add [e1, e2]


nilDataCon, consDataCon :: DataCon
nilDataCon = "[]"
consDataCon = "(:)"

nil :: Term
nil = data_ nilDataCon []

cons :: Var -> Var -> Term
cons x xs = data_ consDataCon [x, xs]


trueDataCon, falseDataCon :: DataCon
trueDataCon = "True"
falseDataCon = "False"

true, false :: Term
true = data_ trueDataCon []
false = data_ falseDataCon []

if_ :: Term -> Term -> Term -> Term
if_ e et ef = case_ e [(DataAlt trueDataCon [], et), (DataAlt falseDataCon [], ef)]

bool :: Bool -> Term
bool x = if x then true else false


nothingDataCon, justDataCon :: DataCon
nothingDataCon = "Nothing"
justDataCon = "Just"

nothing :: Term
nothing = data_ nothingDataCon []

just :: Var -> Term
just x = data_ justDataCon [x]


jDataCon, sDataCon :: DataCon
jDataCon = "J#"
sDataCon = "S#"

j_, s_ :: Var -> Term
j_ x = data_ jDataCon [x]
s_ x = data_ sDataCon [x]


tupleDataCon :: Int -> Maybe DataCon
tupleDataCon 1 = Nothing
tupleDataCon n = Just $ '(' : replicate (n - 1) ',' ++ ")"

unitDataCon, pairDataCon :: DataCon
unitDataCon = fromJust $ tupleDataCon 0
pairDataCon = fromJust $ tupleDataCon 2

unit :: Term
unit = tuple []

tuple :: [Var] -> Term
tuple xs = case tupleDataCon (length xs) of Nothing -> var (expectHead "tuple" xs); Just dc -> data_ dc xs
