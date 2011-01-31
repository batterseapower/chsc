{-# LANGUAGE TupleSections #-}
module Core.Prettify (prettify) where

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Renaming
import Utilities

import Algebra.Lattice

import qualified Data.Map as M
import qualified Data.Set as S


data Occurs = Once | Many
            deriving (Eq)

instance JoinSemiLattice Occurs where
    join _ _ = Many


prettify :: FVedTerm -> FVedTerm
prettify e = snd $ prettifyTerm prettifyIdSupply M.empty (mkIdentityRenaming (S.toList (fvedTermFreeVars e)), e)


type InlineEnv = M.Map (Out Var) (Out FVedTerm)
type OccursEnv = M.Map (Out Var) Occurs

prettifyTerm :: IdSupply -> InlineEnv -> In FVedTerm -> (OccursEnv, Out FVedTerm)
prettifyTerm ids inline (rn, e) = second fvedTerm $ prettifyTerm' ids inline (rn, fvee e)

prettifyTerm' :: IdSupply -> InlineEnv -> In (TermF FVed) -> (OccursEnv, Out (TermF FVed))
prettifyTerm' ids inline (rn, e) = case e of
    Var x -> prettifyVar inline (rn, x)
    Value v -> (occurs, e')
      where (occurs, e') = prettifyValue' ids inline (rn, v)
    App e x -> (M.insertWith join x' Many occurs, App e' x')
      where x' = rename rn x
            (occurs, e') = prettifyTerm ids inline (rn, e)
    PrimOp pop es -> (joins occurss, PrimOp pop es')
      where (occurss, es') = unzip $ map (\e -> prettifyTerm ids inline (rn, e)) es
    Case e alts -> (e_occurs `join` joins alt_occurss, Case e' alts')
      where (e_occurs, e') = prettifyTerm ids inline (rn, e)
            (alt_occurss, alts') = unzip $ map (\alt -> prettifyAlt ids inline (rn, alt)) alts
    LetRec xes e -> (xs' `deleteListMap` occurs', LetRec xes'_leave e')
      where (ids', rn', xes') = renameBounds (\_ x' -> x') ids rn xes
            (xs', in_es) = unzip xes'
            inline' = (xs' `deleteListMap` inline) `M.union` M.fromList xes'_inline
            (es_occurs, es') = unzip $ map (\in_e -> prettifyTerm ids' inline' in_e) in_es
            (e_occurs, e') = prettifyTerm ids' inline' (rn', e)
            occurs' = e_occurs `join` joins es_occurs
            
            -- Inline those bindings that occurred syntactically exactly once (or were dead):
            (xes'_inline, xes'_leave) = partition (\(x', _e') -> maybe True (== Once) (x' `M.lookup` occurs')) (xs' `zip` es')

prettifyVar :: InlineEnv -> In Var -> (OccursEnv, Out (TermF FVed))
prettifyVar inline (rn, x) = (M.singleton x' Once, case M.lookup x' inline of Just e' -> fvee e'; Nothing -> Var x') -- I *think* the substitution is OK, because in the pre-pass my Id threading ensures there is no shadowing
  where x' = rename rn x

prettifyValue' :: IdSupply -> InlineEnv -> In (ValueF FVed) -> (OccursEnv, Out (TermF FVed))
prettifyValue' ids inline (rn, v) = case v of
    Indirect x -> prettifyVar inline (rn, x)
    Lambda x e -> (M.delete x' occurs, Value (Lambda x' e'))
      where (ids', rn', x') = renameBinder ids rn x
            (occurs, e') = prettifyTerm ids' (M.delete x' inline) (rn', e)
    Data dc xs -> (listToMap Many xs', Value (Data dc xs'))
      where xs' = map (rename rn) xs
    Literal l  -> (M.empty, Value (Literal l))

prettifyAlt :: IdSupply -> InlineEnv -> In (AltF FVed) -> (OccursEnv, Out (AltF FVed))
prettifyAlt ids inline (rn, (alt_con, e)) = (bndrs' `deleteListMap` occurs, (alt_con', e'))
  where (ids', rn', alt_con') = renameAltCon ids rn alt_con
        (occurs, e') = prettifyTerm ids' (bndrs' `deleteListMap` inline) (rn', e)
        bndrs' = altConBinders alt_con'
