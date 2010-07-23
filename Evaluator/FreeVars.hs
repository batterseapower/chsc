module Evaluator.FreeVars (
    renamingFreeVars,
    inFreeVars,
    pureHeapFreeVars, pureHeapOpenFreeVars,
    stackFreeVars, stackFrameFreeVars,
    stateFreeVars
  ) where

import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming

import Renaming
import Utilities

import qualified Data.Map as M
import qualified Data.Set as S


renamingFreeVars :: Renaming -> FreeVars -> FreeVars
renamingFreeVars rn fvs = S.map (rename rn) fvs

inFreeVars :: (a -> FreeVars) -> In a -> FreeVars
inFreeVars thing_fvs (rn, thing) = renamingFreeVars rn (thing_fvs thing)

pureHeapFreeVars :: PureHeap -> (BoundVars, FreeVars) -> FreeVars
pureHeapFreeVars h (bvs, fvs) = fvs' S.\\ bvs'
  where (bvs', fvs') = pureHeapOpenFreeVars h (bvs, fvs)

pureHeapOpenFreeVars :: PureHeap -> (BoundVars, FreeVars) -> (BoundVars, FreeVars)
pureHeapOpenFreeVars = flip $ M.foldWithKey (\x' in_e (bvs, fvs) -> (S.insert x' bvs, fvs `S.union` inFreeVars taggedTermFreeVars in_e))

stackFreeVars :: Stack -> FreeVars -> (BoundVars, FreeVars)
stackFreeVars k fvs = (S.unions *** (S.union fvs . S.unions)) . unzip . map (stackFrameFreeVars) $ k

stackFrameFreeVars :: StackFrame -> (BoundVars, FreeVars)
stackFrameFreeVars kf = case kf of
    Apply x'                -> (S.empty, S.singleton (tagee x'))
    Scrutinise in_alts      -> (S.empty, inFreeVars taggedAltsFreeVars in_alts)
    PrimApply _ in_vs in_es -> (S.empty, S.unions (map (inFreeVars taggedValueFreeVars . tagee) in_vs) `S.union` S.unions (map (inFreeVars taggedTermFreeVars) in_es))
    Update x'               -> (S.singleton (tagee x'), S.empty)

stateFreeVars :: State -> FreeVars
stateFreeVars (Heap h _, k, in_e) = pureHeapFreeVars h (stackFreeVars k (inFreeVars taggedTermFreeVars in_e))
