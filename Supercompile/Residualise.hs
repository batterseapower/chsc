{-# LANGUAGE ViewPatterns #-}
module Supercompile.Residualise where

import Evaluator.Syntax

import Core.Renaming
import Core.Syntax

import Utilities

import qualified Data.Map as M


residualiseState :: State -> Out Term
residualiseState (heap, k, in_e) = residualiseHeap heap (\ids -> residualiseStack ids k (detagTerm (renameIn renameTaggedTerm ids in_e)))

residualiseHeap :: Heap -> (IdSupply -> ([(Out Var, Out Term)], Out Term)) -> Out Term
residualiseHeap (Heap h ids) (($ ids) -> (floats, e)) = letRec (residualisePureHeap ids h ++ floats) e

residualisePureHeap :: IdSupply -> PureHeap -> [(Out Var, Out Term)]
residualisePureHeap ids h = [(x', detagTerm $ renameIn renameTaggedTerm ids in_e) | (x', in_e) <- M.toList h]

residualiseStack :: IdSupply -> Stack -> Out Term -> ([(Out Var, Out Term)], Out Term)
residualiseStack _   []     e = ([], e)
residualiseStack ids (kf:k) (residualiseStackFrame ids (tagee kf) -> (floats, e)) = first (floats ++) $ residualiseStack ids k e

residualiseStackFrame :: IdSupply -> StackFrame -> Out Term -> ([(Out Var, Out Term)], Out Term)
residualiseStackFrame _   (Apply x2')               e1 = ([], e1 `app` x2')
residualiseStackFrame ids (Scrutinise in_alts)      e  = ([], case_ e (detagAlts $ renameIn renameTaggedAlts ids in_alts))
residualiseStackFrame ids (PrimApply pop in_vs es') e  = ([], primOp pop (map (value . detagValue . renameIn renameTaggedValue ids) in_vs ++ [e] ++ map (detagTerm . renameIn renameTaggedTerm ids) es'))
residualiseStackFrame _   (Update x')               e  = ([(x', e)], var x')
