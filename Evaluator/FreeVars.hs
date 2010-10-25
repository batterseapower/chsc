module Evaluator.FreeVars (
    inFreeVars,
    pureHeapFreeVars, pureHeapOpenFreeVars,
    stackFreeVars, stackFrameFreeVars,
    stateFreeVars
  ) where

import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming

import Utilities

import qualified Data.Map as M
import qualified Data.Set as S


inFreeVars :: (a -> FreeVarsF ann) -> In a -> FreeVarsF ann
inFreeVars thing_fvs (rn, thing) = renameFreeVars rn (thing_fvs thing)

pureHeapFreeVars :: PureHeap -> (BoundVars, FreeVars) -> FreeVars
pureHeapFreeVars h (bvs, fvs) = fvs' `exclude` bvs'
  where (bvs', fvs') = pureHeapOpenFreeVars h (bvs, fvs)

pureHeapOpenFreeVars :: PureHeap -> (BoundVars, FreeVars) -> (BoundVars, FreeVars)
pureHeapOpenFreeVars = flip $ M.foldWithKey (\x' in_e (bvs, fvs) -> (S.insert x' bvs, fvs `unionFreeVars` inFreeVars annedTermFreeVars in_e))

stackFreeVars :: Stack -> FreeVars -> (BoundVars, FreeVars)
stackFreeVars k fvs = (S.unions *** (unionFreeVars fvs . unionsFreeVars)) . unzip . map stackFrameFreeVars $ k

stackFrameFreeVars :: StackFrame -> (BoundVars, FreeVars)
stackFrameFreeVars kf = case kf of
    Apply x'                -> (S.empty, annedFreeVars x')
    Scrutinise in_alts      -> (S.empty, inFreeVars annedAltsFreeVars in_alts)
    PrimApply _ in_vs in_es -> (S.empty, unionsFreeVars (map (inFreeVars annedValueFreeVars) in_vs) `unionFreeVars` unionsFreeVars (map (inFreeVars annedTermFreeVars) in_es))
    Update x'               -> (S.singleton (annee x'), emptyFreeVars)

stateFreeVars :: State -> FreeVars
stateFreeVars (Heap h _, k, in_e) = pureHeapFreeVars h (stackFreeVars k (inFreeVars annedTermFreeVars in_e))
