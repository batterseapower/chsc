{-# LANGUAGE ViewPatterns #-}
module Supercompile.Residualise where

import Evaluator.Syntax

import Core.Renaming
import Core.Syntax

import Utilities

import qualified Data.Map as M


residualiseState :: State -> Out Term
residualiseState (heap, k, in_e) = residualiseHeap heap (\ids -> residualiseStack ids k (detagAnnedTerm (renameIn renameAnnedTerm ids in_e)))

residualiseHeap :: Heap -> (IdSupply -> ([(Out Var, Out Term)], Out Term)) -> Out Term
residualiseHeap (Heap h ids) (($ ids) -> (floats, e)) = letRecSmart (residualisePureHeap ids h ++ floats) e

residualisePureHeap :: IdSupply -> PureHeap -> [(Out Var, Out Term)]
residualisePureHeap ids h = [(x', detagAnnedTerm $ renameIn renameAnnedTerm ids in_e) | (x', in_e) <- M.toList h]

residualiseStack :: IdSupply -> Stack -> Out Term -> ([(Out Var, Out Term)], Out Term)
residualiseStack _   []     e = ([], e)
residualiseStack ids (kf:k) (residualiseStackFrame ids kf -> (floats, e)) = first (floats ++) $ residualiseStack ids k e

residualiseStackFrame :: IdSupply -> StackFrame -> Out Term -> ([(Out Var, Out Term)], Out Term)
residualiseStackFrame _   (Apply x2')               e1 = ([], e1 `app` annee x2')
residualiseStackFrame ids (Scrutinise in_alts)      e  = ([], case_ e (detagAnnedAlts $ renameIn renameAnnedAlts ids in_alts))
residualiseStackFrame ids (PrimApply pop in_vs es') e  = ([], primOp pop (map (value . unI . detagAnnedValue . renameIn renameAnnedValue ids) in_vs ++ e : map (detagAnnedTerm . renameIn renameAnnedTerm ids) es'))
residualiseStackFrame _   (Update x')               e  = ([(annee x', e)], var (annee x'))
