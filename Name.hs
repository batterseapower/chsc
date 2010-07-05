module Name (
    Name(..), name,
    freshName, freshNames
  ) where

import Utilities

import Data.Char
import Data.Function
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
    (==) = (==) `on` name_key

instance Ord Name where
    compare = comparing name_key

instance Pretty Name where
    pPrintPrec level _ n = text (escape $ name_string n) <> maybe empty (\i -> text "_" <> text (show i)) (name_id n)
      where escape | level == haskellLevel = concatMap escapeHaskellChar
                   | otherwise             = id
            escapeHaskellChar c
              | c == 'z'                             = "zz"
              | isAlphaNum c || c `elem` ['_', '\''] = [c]
              | otherwise                            = 'z' : show (ord c)

name_key :: Name -> Either String Id
name_key n = maybe (Left $ name_string n) Right (name_id n)

name :: String -> Name
name s = Name s Nothing

freshName :: IdSupply -> String -> (IdSupply, Name)
freshName ids s = second (Name s . Just) $ stepIdSupply ids

freshNames :: IdSupply -> [String] -> (IdSupply, [Name])
freshNames = mapAccumL freshName
