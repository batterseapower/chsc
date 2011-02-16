module Name (
    Name(..), name,
    freshName, freshNames
  ) where

import Utilities

import Data.Char
import Data.Ord


data Name = Name {
    name_string :: String,
    name_id :: Maybe Id
  }

instance NFData Name where
    rnf (Name a b) = rnf a `seq` rnf b

instance Show Name where
    show n = "(name " ++ show (show (pPrint n)) ++ ")"

instance Eq Name where
    -- I used to inject into Either String Id as an intermidate step but the resulting name_key function
    -- accounted for like 88% of total allocation. Write it direct style for performance:
    n1 == n2 = case (name_id n1, name_id n2) of
        (Nothing, Nothing)   -> name_string n1 == name_string n2
        (Just id1, Just id2) -> id1 == id2
        _                    -> False

instance Ord Name where
    n1 `compare` n2 = case (name_id n1, name_id n2) of
        (Nothing, Nothing)   -> name_string n1 `compare` name_string n2
        (Just id1, Just id2) -> id1 `compare` id2
        (Just _, Nothing)    -> GT
        (Nothing, Just _)    -> LT

instance Pretty Name where
    pPrintPrec level _ n = text (escape $ name_string n) <> maybe empty (\i -> text "_" <> text (show i)) (name_id n)
      where escape | level == haskellLevel = concatMap escapeHaskellChar
                   | otherwise             = id
            escapeHaskellChar c
              | c == 'z'                             = "zz"
              | isAlphaNum c || c `elem` ['_', '\''] = [c]
              | otherwise                            = 'z' : show (ord c)

name :: String -> Name
name s = Name s Nothing

freshName :: IdSupply -> String -> (IdSupply, Name)
freshName ids s = second (Name s . Just) $ stepIdSupply ids

freshNames :: IdSupply -> [String] -> (IdSupply, [Name])
freshNames = mapAccumL freshName
