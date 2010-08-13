module Core.Counted where

import Core.Syntax

import Utilities


data Counted a = Counted { count :: Int, countee :: a }

instance Show1 Counted where
    showsPrec1 prec (Counted c x) = showParen (prec >= appPrec) (showString "Counted" . showsPrec appPrec c . showsPrec appPrec x)

instance Eq1 Counted where
    eq1 (Counted c1 x1) (Counted c2 x2) = c1 == c2 && x1 == x2

instance Ord1 Counted where
    compare1 (Counted c1 x1) (Counted c2 x2) = (c1, x1) `compare` (c2, x2)

instance NFData1 Counted where
    rnf1 (Counted a b) = rnf a `seq` rnf b

instance Pretty1 Counted where
    pPrintPrec1 level _prec (Counted count x) = text ("[" ++ show count ++ "]") <> pPrintPrec level appPrec x

instance Functor Counted where
    fmap f (Counted c x) = Counted c (f x)


type CountedTerm = Counted (TermF Counted)
type CountedAlt = AltF Counted
type CountedValue = ValueF Counted