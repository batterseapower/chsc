{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Core.Statics where

import Core.Syntax (Var)
import Core.Renaming (Out)

import StaticFlags
import Utilities

import qualified Data.Map as M
import qualified Data.Set as S


data StaticSort = HFunction | LocalVariable Tag | InputVariable

instance Pretty StaticSort where
    pPrint HFunction           = text "(h-function static)"
    pPrint (LocalVariable _tg) = text "(local variable static)"
    pPrint InputVariable       = text "(input variable static)"


-- | We do not abstract the h functions over these variables. This helps typechecking and gives GHC a chance to inline the definitions.
newtype Statics = Statics { staticVars :: M.Map (Out Var) StaticSort }
                deriving (Pretty)

mkTopLevelStatics :: M.Map (Out Var) StaticSort -> Statics
mkTopLevelStatics = Statics

extendStatics :: Statics -> M.Map (Out Var) StaticSort -> Statics
extendStatics (Statics xs) ys | lOCAL_TIEBACKS = Statics (xs `M.union` ys)
                              | otherwise      = Statics xs

excludeStatics :: Statics -> S.Set (Out Var) -> Statics
excludeStatics (Statics xs) ys = Statics (xs `exclude` ys)

restrictStatics :: Statics -> S.Set (Out Var) -> Statics
restrictStatics (Statics xs) ys = Statics (xs `restrict` ys)

isStatic :: Var -> Statics -> Bool
isStatic x xs = x `M.member` staticVars xs
