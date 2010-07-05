{-# LANGUAGE ViewPatterns, TupleSections #-}
module Core.Renaming where

import Core.Syntax

import Renaming
import Utilities


type In a = (Renaming, a)
type Out a = a


renameTagged :: (IdSupply -> Renaming -> a -> a) -> IdSupply -> Renaming -> Tagged a -> Tagged a
renameTagged f ids rn (Tagged tg x) = Tagged tg (f ids rn x)

renameTaggedBinder :: (IdSupply -> Renaming -> a -> (IdSupply, Renaming, a)) -> IdSupply -> Renaming -> Tagged a -> (IdSupply, Renaming, Tagged a)
renameTaggedBinder f ids rn (Tagged tg x) = third3 (Tagged tg) $ f ids rn x


renameIn :: (IdSupply -> Renaming -> a -> a) -> IdSupply -> In a -> a
renameIn f ids (rn, x) = f ids rn x

renameInRenaming :: Renaming -> In a -> In a
renameInRenaming rn_by (rn, x) = (renameRenaming rn_by rn, x)

renameBounds :: (Var -> Var -> v) -> IdSupply -> Renaming -> [(Var, a)] -> (IdSupply, Renaming, [(v, In a)])
renameBounds f ids rn (unzip -> (xs, es)) = (ids', rn', zipWith f xs xs' `zip` map (rn',) es)
  where (ids', rn', xs') = renameBinders ids rn xs


renameValue :: IdSupply -> Renaming -> Value -> Value
renameValue = renameValue' renameTerm

renameTaggedValue :: IdSupply -> Renaming -> TaggedValue -> TaggedValue
renameTaggedValue = renameValue' renameTaggedTerm

renameValue' :: (IdSupply -> Renaming -> term -> term)
             -> IdSupply -> Renaming -> ValueF term -> ValueF term
renameValue' term ids rn v = case v of
    Lambda x e -> Lambda x' (term ids' rn' e)
      where (ids', rn', x') = renameBinder ids rn x
    Data dc xs -> Data dc (map (rename rn) xs)
    Literal l -> Literal l

renameTerm :: IdSupply -> Renaming -> Term -> Term
renameTerm ids rn (Term e) = Term $ renameTerm' renameTerm ids rn e

renameTaggedTerm :: IdSupply -> Renaming -> TaggedTerm -> TaggedTerm
renameTaggedTerm ids rn (TaggedTerm e) = TaggedTerm $ renameTagged (renameTerm' renameTaggedTerm) ids rn e

renameTerm' :: (IdSupply -> Renaming -> term -> term)
            -> IdSupply -> Renaming -> TermF term -> TermF term
renameTerm' term ids rn e = case e of
    Var x -> Var (safeRename "renameTerm" rn x)
    Value v -> Value (renameValue' term ids rn v)
    App e1 x2 -> App (term ids rn e1) (rename rn x2)
    PrimOp pop es -> PrimOp pop (map (term ids rn) es)
    Case e alts -> Case (term ids rn e) (renameAlts' term ids rn alts)
    LetRec xes e -> LetRec (map (second (renameIn term ids')) xes') (term ids' rn' e)
      where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes

renameAlt :: IdSupply -> Renaming -> Alt -> Alt
renameAlt = renameAlt' renameTerm

renameAlt' :: (IdSupply -> Renaming -> term -> term)
           -> IdSupply -> Renaming -> AltF term -> AltF term
renameAlt' term ids rn (alt_con, alt_e) = (alt_con', term ids' rn' alt_e)
  where (ids', rn', alt_con') = renameAltCon ids rn alt_con

renameAltCon :: IdSupply -> Renaming -> AltCon -> (IdSupply, Renaming, AltCon)
renameAltCon ids rn_alt alt_con = case alt_con of
    DataAlt alt_dc alt_xs -> third3 (DataAlt alt_dc) $ renameBinders ids rn_alt alt_xs
    LiteralAlt _          -> (ids, rn_alt, alt_con)
    DefaultAlt alt_mb_x   -> maybe (ids, rn_alt, alt_con) (third3 (DefaultAlt . Just) . renameBinder ids rn_alt) alt_mb_x

renameAlts :: IdSupply -> Renaming -> [Alt] -> [Alt]
renameAlts = renameAlts' renameTerm

renameTaggedAlts :: IdSupply -> Renaming -> [TaggedAlt] -> [TaggedAlt]
renameTaggedAlts = renameAlts' renameTaggedTerm

renameAlts' :: (IdSupply -> Renaming -> term -> term)
            -> IdSupply -> Renaming -> [AltF term] -> [AltF term]
renameAlts' term ids rn = map (renameAlt' term ids rn)
