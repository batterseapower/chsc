{-# LANGUAGE Rank2Types #-}
module Core.FreeVars where

import Core.Syntax

import Utilities

import qualified Data.Set as S


type FreeVars = S.Set Var
type BoundVars = S.Set Var

deleteList :: Ord a => [a] -> S.Set a -> S.Set a
deleteList = flip $ foldr S.delete


(termFreeVars,       altsFreeVars,       valueFreeVars)       = mkFreeVars (\f (I e) -> f e)
(taggedTermFreeVars, taggedAltsFreeVars, taggedValueFreeVars) = mkFreeVars (\f (Tagged _ e) -> f e)

{-# INLINE mkFreeVars #-}
mkFreeVars :: (forall a. (a -> FreeVars) -> ann a -> FreeVars)
           -> (ann (TermF ann) -> FreeVars,
               [AltF ann]      -> FreeVars,
               ValueF ann      -> FreeVars)
mkFreeVars rec = (term, alternatives, value)
  where
    var = rec var'
    var' x = S.singleton x
    
    term = rec term'
    term' (Var x)        = S.singleton x
    term' (Value v)      = value v
    term' (App e x)      = term e `S.union` var x
    term' (PrimOp _ es)  = S.unions $ map term es
    term' (Case e alts)  = term e `S.union` alternatives alts
    term' (LetRec xes e) = deleteList xs $ S.unions (map term es) `S.union` term e
      where (xs, es) = unzip xes
    
    value (Lambda x e) = S.delete x $ term e
    value (Data _ xs)  = S.fromList xs
    value (Literal _)  = S.empty
    
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
