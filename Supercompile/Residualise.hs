{-# LANGUAGE ViewPatterns #-}
module Supercompile.Residualise where

import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Utilities

import qualified Data.Map as M


residualiseState :: State -> Out FVedTerm
residualiseState (heap, k, in_e) = residualiseHeap heap (\ids -> residualiseStack ids k (detagAnnedTerm (renameIn renameAnnedTerm ids in_e)))

residualiseHeap :: Heap -> (IdSupply -> (Out [(Var, FVedTerm)], FVedTerm)) -> FVedTerm
residualiseHeap (Heap h ids) (($ ids) -> (floats, e)) = letRecSmart (residualisePureHeap ids h ++ floats) e

residualisePureHeap :: IdSupply -> PureHeap -> Out [(Var, FVedTerm)]
residualisePureHeap ids h = [(x', e') | (x', hb) <- M.toList h, Just e' <- [residualiseHeapBinding ids hb]]

residualiseHeapBinding :: IdSupply -> HeapBinding -> Maybe (Out FVedTerm)
residualiseHeapBinding ids hb = do { Concrete (Here in_e) <- return hb; return (detagAnnedTerm $ renameIn renameAnnedTerm ids in_e) }

residualiseStack :: IdSupply -> Stack -> Out FVedTerm -> (Out [(Var, FVedTerm)], Out FVedTerm)
residualiseStack _   []     e = ([], e)
residualiseStack ids (kf:k) (residualiseStackFrame ids kf -> (floats, e)) = first (floats ++) $ residualiseStack ids k e

residualiseStackFrame :: IdSupply -> StackFrame -> Out FVedTerm -> (Out [(Var, FVedTerm)], Out FVedTerm)
residualiseStackFrame _   (Apply x2')               e1 = ([], e1 `app` annee x2')
residualiseStackFrame ids (Scrutinise in_alts)      e  = ([], case_ e (detagAnnedAlts $ renameIn renameAnnedAlts ids in_alts))
residualiseStackFrame ids (PrimApply pop in_vs es') e  = ([], primOp pop (map (value . fvee . detagAnnedValue . renameIn renameAnnedValue ids) in_vs ++ e : map (detagAnnedTerm . renameIn renameAnnedTerm ids) es'))
residualiseStackFrame _   (Update x')               e  = ([(annee x', e)], var (annee x'))
