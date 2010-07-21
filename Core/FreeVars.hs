module Core.FreeVars where

import Core.Syntax

import Utilities

import qualified Data.Set as S


type FreeVars = S.Set Var
type BoundVars = S.Set Var

deleteList :: Ord a => [a] -> S.Set a -> S.Set a
deleteList = flip $ foldr S.delete

termFreeVars :: Term -> FreeVars
termFreeVars (I e) = termFreeVars' termFreeVars e

taggedTermFreeVars :: TaggedTerm -> FreeVars
taggedTermFreeVars (Tagged _ e) = termFreeVars' taggedTermFreeVars e

termFreeVars' :: (ann (TermF ann) -> FreeVars) -> TermF ann -> FreeVars
termFreeVars' _    (Var x)        = S.singleton x
termFreeVars' term (Value v)      = valueFreeVars' term v
termFreeVars' term (App e x)      = S.insert x $ term e
termFreeVars' term (PrimOp _ es)  = S.unions $ map term es
termFreeVars' term (Case e alts)  = term e `S.union` altsFreeVars' term alts
termFreeVars' term (LetRec xes e) = deleteList xs $ S.unions (map term es) `S.union` term e
  where (xs, es) = unzip xes

altConOpenFreeVars :: AltCon -> (BoundVars, FreeVars) -> (BoundVars, FreeVars)
altConOpenFreeVars (DataAlt _ xs)    (bvs, fvs) = (bvs `S.union` S.fromList xs, fvs)
altConOpenFreeVars (LiteralAlt _)    (bvs, fvs) = (bvs, fvs)
altConOpenFreeVars (DefaultAlt mb_x) (bvs, fvs) = (maybe id S.insert mb_x bvs, fvs)

altConFreeVars :: AltCon -> FreeVars -> FreeVars
altConFreeVars (DataAlt _ xs)    = deleteList xs
altConFreeVars (LiteralAlt _)    = id
altConFreeVars (DefaultAlt mb_x) = maybe id S.delete mb_x

altFreeVars :: Alt -> FreeVars
altFreeVars = altFreeVars' termFreeVars

altFreeVars' :: (ann (TermF ann) -> FreeVars) -> AltF ann -> FreeVars
altFreeVars' term (altcon, e) = altConFreeVars altcon $ term e

altsFreeVars :: [Alt] -> FreeVars
altsFreeVars = altsFreeVars' termFreeVars

taggedAltsFreeVars :: [TaggedAlt] -> FreeVars
taggedAltsFreeVars = altsFreeVars' taggedTermFreeVars

altsFreeVars' :: (ann (TermF ann) -> FreeVars) -> [AltF ann] -> FreeVars
altsFreeVars' term = S.unions . map (altFreeVars' term)

valueFreeVars :: Value -> FreeVars
valueFreeVars = valueFreeVars' termFreeVars

taggedValueFreeVars :: TaggedValue -> FreeVars
taggedValueFreeVars = valueFreeVars' taggedTermFreeVars

valueFreeVars' :: (ann (TermF ann) -> FreeVars) -> ValueF ann -> FreeVars
valueFreeVars' term (Lambda x e) = S.delete x $ term e
valueFreeVars' _    (Data _ xs)  = S.fromList xs
valueFreeVars' _    (Literal _)  = S.empty
