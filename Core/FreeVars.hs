{-# LANGUAGE Rank2Types, TypeOperators, FlexibleInstances, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
module Core.FreeVars where

import Core.Syntax

import Utilities

import qualified Data.Set as S
import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable


type FreeVars = S.Set Var
type BoundVars = S.Set Var


(termVarFreeVars',       termFreeVars,           termFreeVars',           altsFreeVars,           valueFreeVars,           valueFreeVars')           = mkFreeVars (\f (I e) -> f e)
(fvedTermVarFreeVars',   fvedTermFreeVars,       fvedTermFreeVars',       fvedAltsFreeVars,       fvedValueFreeVars,       fvedValueFreeVars')       = mkFreeVars (\_ (FVed fvs _) -> fvs)
(taggedTermVarFreeVars', taggedTermFreeVars,     taggedTermFreeVars',     taggedAltsFreeVars,     taggedValueFreeVars,     taggedValueFreeVars')     = mkFreeVars (\f (Tagged _ e) -> f e)
(taggedFVedVarFreeVars', taggedFVedTermFreeVars, taggedFVedTermFreeVars', taggedFVedAltsFreeVars, taggedFVedValueFreeVars, taggedFVedValueFreeVars') = mkFreeVars (\_ (Comp (Tagged _ (FVed fvs _))) -> fvs)

{-# INLINE mkFreeVars #-}
mkFreeVars :: (forall a. (a -> FreeVars) -> ann a -> FreeVars)
           -> (Var              -> FreeVars,
               ann (TermF ann)  -> FreeVars,
               TermF ann        -> FreeVars,
               [AltF ann]       -> FreeVars,
               ann (ValueF ann) -> FreeVars,
               ValueF ann       -> FreeVars)
mkFreeVars rec = (var', term, term', alternatives, value, value')
  where
    var = rec var'
    var' = S.singleton
    
    term = rec term'
    term' (Var x)        = S.singleton x
    term' (Value v)      = value' v
    term' (App e x)      = term e `S.union` var x
    term' (PrimOp _ es)  = S.unions $ map term es
    term' (Case e alts)  = term e `S.union` alternatives alts
    term' (LetRec xes e) = deleteList xs $ S.unions (map term es) `S.union` term e
      where (xs, es) = unzip xes
    
    value = rec value'
    value' (Lambda x e) = S.delete x $ term e
    value' (Data _ xs)  = S.fromList xs
    value' (Literal _)  = S.empty
    
    alternatives = S.unions . map alternative
    
    alternative (altcon, e) = altConFreeVars altcon $ term e

altConOpenFreeVars :: AltCon -> (BoundVars, FreeVars) -> (BoundVars, FreeVars)
altConOpenFreeVars (DataAlt _ xs)    (bvs, fvs) = (bvs `S.union` S.fromList xs, fvs)
altConOpenFreeVars (LiteralAlt _)    (bvs, fvs) = (bvs, fvs)
altConOpenFreeVars (DefaultAlt mb_x) (bvs, fvs) = (maybe id S.insert mb_x bvs, fvs)

altConFreeVars :: AltCon -> FreeVars -> FreeVars
altConFreeVars (DataAlt _ xs)    = deleteList xs
altConFreeVars (LiteralAlt _)    = id
altConFreeVars (DefaultAlt mb_x) = maybe id S.delete mb_x


data FVed a = FVed { freeVars :: !FreeVars, fvee :: !a }
            deriving (Functor, Foldable.Foldable, Traversable.Traversable)

instance Copointed FVed where
    extract = fvee

instance Show1 FVed where
    showsPrec1 prec (FVed fvs x) = showParen (prec >= appPrec) (showString "FVed" . showsPrec appPrec fvs . showsPrec appPrec x)

instance Eq1 FVed where
    eq1 (FVed fvs1 x1) (FVed fvs2 x2) = fvs1 == fvs2 && x1 == x2

instance Ord1 FVed where
    compare1 (FVed fvs1 x1) (FVed fvs2 x2) = (x1, fvs1) `compare` (x2, fvs2)

instance NFData1 FVed where
    rnf1 (FVed a b) = rnf a `seq` rnf b

instance Pretty1 FVed where
    pPrintPrec1 level prec (FVed _ x) = pPrintPrec level prec x


type FVedTerm = FVed (TermF FVed)
type FVedAlt = AltF FVed
type FVedValue = ValueF FVed


instance Symantics FVed where
    var = fvedTerm . Var
    value = fvedTerm . Value
    app e x = fvedTerm (App e (fvedVar x))
    primOp pop = fvedTerm . PrimOp pop
    case_ e = fvedTerm . Case e
    letRec xes e = fvedTerm (LetRec xes e)

fvedVar :: Var -> FVed Var
fvedVar x = FVed (taggedTermVarFreeVars' x) x

fvedTerm :: TermF FVed -> FVedTerm
fvedTerm e = FVed (fvedTermFreeVars' e) e


type TaggedFVedTerm = (Tagged :.: FVed) (TermF (Tagged :.: FVed))
type TaggedFVedAlt = AltF (Tagged :.: FVed)
type TaggedFVedValue = ValueF (Tagged :.: FVed)
