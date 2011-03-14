{-# LANGUAGE ViewPatterns, TupleSections #-}
module Evaluator.Residualise (pPrintHeap, pPrintFullState, pPrintFullUnnormalisedState) where

import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming
import Core.Syntax

import Utilities

import Data.Either
import qualified Data.Map as M


residualiseTerm :: IdSupply -> In AnnedTerm -> Out FVedTerm
residualiseTerm ids = detagAnnedTerm . renameIn (renameAnnedTerm ids)

residualiseHeap :: Heap -> (IdSupply -> ((Out [(Var, Doc)], Out [(Var, FVedTerm)]), Out FVedTerm)) -> (Out [(Var, Doc)], Out FVedTerm)
residualiseHeap (Heap h ids) (($ ids) -> ((floats_static_k, floats_nonstatic_k), e)) = (floats_static_h ++ floats_static_k, letRecSmart (floats_nonstatic_h ++ floats_nonstatic_k) e)
  where (floats_static_h, floats_nonstatic_h) = residualisePureHeap ids h

residualisePureHeap :: IdSupply -> PureHeap -> (Out [(Var, Doc)], Out [(Var, FVedTerm)])
residualisePureHeap ids h = partitionEithers [fmapEither (x',) (x',) (residualiseHeapBinding ids hb) | (x', hb) <- M.toList h]

residualiseHeapBinding :: IdSupply -> HeapBinding -> Either (Out Doc) (Out FVedTerm)
residualiseHeapBinding ids (HB InternallyBound (Right in_e)) = Right (residualiseTerm ids in_e)
residualiseHeapBinding _   hb                                = Left (pPrint hb)

residualiseStack :: IdSupply -> Stack -> Out FVedTerm -> ((Out [(Var, Doc)], Out [(Var, FVedTerm)]), Out FVedTerm)
residualiseStack _   []     e = (([], []), e)
residualiseStack ids (kf:k) (residualiseStackFrame ids (tagee kf) -> ((static_floats, nonstatic_floats), e)) = first ((static_floats ++) *** (nonstatic_floats ++)) $ residualiseStack ids k e

residualiseStackFrame :: IdSupply -> StackFrame -> Out FVedTerm -> ((Out [(Var, Doc)], Out [(Var, FVedTerm)]), Out FVedTerm)
residualiseStackFrame _   (Apply x2')               e1 = (([], []), e1 `app` x2')
residualiseStackFrame ids (Scrutinise in_alts)      e  = (([], []), case_ e (detagAnnedAlts $ renameIn (renameAnnedAlts ids) in_alts))
residualiseStackFrame ids (PrimApply pop in_vs es') e  = (([], []), primOp pop (map (value . fvee . detagAnnedValue . renameIn (renameAnnedValue ids)) in_vs ++ e : map (residualiseTerm ids) es'))
residualiseStackFrame _   (Update x')               e  = (([], [(x', e)]), var x')


pPrintHeap :: Heap -> Doc
pPrintHeap (Heap h ids) = pPrint $ floats_static_h ++ [(x, pPrint e) | (x, e) <- floats_nonstatic_h]
  where (floats_static_h, floats_nonstatic_h) = residualisePureHeap ids h

pPrintFullState :: State -> Doc
pPrintFullState = pPrintFullUnnormalisedState . denormalise

pPrintFullUnnormalisedState :: UnnormalisedState -> Doc
pPrintFullUnnormalisedState (deeds, heap, k, in_e) = text "Deeds:" <+> pPrint deeds $$ pPrint (M.fromList floats_static) $$ pPrint e
  where (floats_static, e) = residualiseHeap heap (\ids -> residualiseStack ids k (residualiseTerm ids in_e))

