{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards, NoMonoPatBinds #-}
module Evaluator.FreeVars (
    WhyLive(..), Liveness,
    emptyLiveness, plusLiveness, plusLivenesses,
    whyLive,

    inFreeVars,
    heapBindingReferences, heapBindingLiveness,
    pureHeapBoundVars, stackBoundVars, stackFrameBoundVars,
    stateLiveness, stateFreeVars, stateStaticBinders, stateStaticBindersAndFreeVars, pureHeapBinders
  ) where

import Evaluator.Deeds
import Evaluator.Syntax

import Core.Syntax
import Core.FreeVars
import Core.Renaming

import Utilities

import Algebra.Lattice

import qualified Data.Map as M
import qualified Data.Set as S


newtype Liveness = Liveness { unLiveness :: M.Map (Out Var) WhyLive }
                 deriving (Eq, JoinSemiLattice, BoundedJoinSemiLattice)

instance Pretty Liveness where
    pPrintPrec level prec = pPrintPrec level prec . unLiveness

mkLiveness :: FreeVars -> WhyLive -> Liveness
mkLiveness fvs why_live = Liveness $ setToMap why_live fvs

emptyLiveness :: Liveness
emptyLiveness = bottom

plusLiveness :: Liveness -> Liveness -> Liveness
plusLiveness = join

plusLivenesses :: [Liveness] -> Liveness
plusLivenesses = joins

whyLive :: Out Var -> Liveness -> Maybe WhyLive
whyLive x' live = x' `M.lookup` unLiveness live


inFreeVars :: (a -> FreeVars) -> In a -> FreeVars
inFreeVars thing_fvs (rn, thing) = renameFreeVars rn (thing_fvs thing)

-- | Finds the set of things "referenced" by a 'HeapBinding': this is only used to construct tag-graphs
heapBindingReferences :: HeapBinding -> FreeVars
heapBindingReferences Environmental    = S.empty
heapBindingReferences (Updated _ fvs)  = fvs
heapBindingReferences (Phantom in_e)   = inFreeVars annedTermFreeVars in_e
heapBindingReferences (Concrete in_e)  = inFreeVars annedTermFreeVars in_e
heapBindingReferences (Unfolding in_v) = inFreeVars annedValueFreeVars in_v

-- NB: reporting the FVs of an Updated thing as live is bad. In particular:
--  1) It causes us to abstract over too many free variables, because transitiveInline will pull in
--     things the update frame "references" as phantom bindings, even if they are otherwise dead.
--  2) It causes assert failures in the matcher because we find ourselves unable to rename the free
--     variables of the phantom bindings thus pulled in (they are dead, so the matcher doesn't get to them)
heapBindingLiveness :: HeapBinding -> Liveness
heapBindingLiveness hb = case heapBindingTerm hb of
    Nothing               -> emptyLiveness
    Just (in_e, why_live) -> mkLiveness (inFreeVars annedTermFreeVars in_e) why_live

-- | Returns all the variables bound by the heap that we might have to residualise in the splitter
pureHeapBoundVars :: PureHeap -> BoundVars
pureHeapBoundVars = M.keysSet -- I think its harmless to include variables bound by phantoms in this set

-- | Returns all the variables bound by the stack that we might have to residualise in the splitter
stackBoundVars :: Stack -> BoundVars
stackBoundVars = S.unions . map (stackFrameBoundVars . tagee)

stackFrameBoundVars :: StackFrame -> BoundVars
stackFrameBoundVars = fst . stackFrameOpenFreeVars

stackFrameOpenFreeVars :: StackFrame -> (BoundVars, FreeVars)
stackFrameOpenFreeVars kf = case kf of
    Apply x'                -> (S.empty, S.singleton x')
    Scrutinise in_alts      -> (S.empty, inFreeVars annedAltsFreeVars in_alts)
    PrimApply _ in_vs in_es -> (S.empty, S.unions (map (inFreeVars annedValueFreeVars) in_vs) `S.union` S.unions (map (inFreeVars annedTermFreeVars) in_es))
    Update x'               -> (S.singleton x', S.empty)

-- | Returns (an overapproximation of) the free variables of the state that it would be useful to inline, and why that is so
stateLiveness :: (Deeds, Heap, Stack, In (Anned a)) -> Liveness
stateLiveness state = mkLiveness (stateFreeVars state) ConcreteLive

-- | Returns (an overapproximation of) the free variables that the state would have if it were residualised right now (i.e. variables bound by phantom bindings *are* in the free vars set)
stateFreeVars :: (Deeds, Heap, Stack, In (Anned a)) -> FreeVars
stateFreeVars = snd . stateStaticBindersAndFreeVars

stateStaticBinders :: (Deeds, Heap, Stack, In (Anned a)) -> BoundVars
stateStaticBinders = fst . stateStaticBindersAndFreeVars

-- | Returns the free variables that the state would have if it were residualised right now (i.e. excludes static binders),
-- along with the static binders as a separate set.
stateStaticBindersAndFreeVars :: (Deeds, Heap, Stack, In (Anned a)) -> (BoundVars, FreeVars)
pureHeapBinders :: PureHeap -> BoundVars
(stateStaticBindersAndFreeVars, pureHeapBinders) = (\(_, Heap h _, k, in_e) -> case pureHeapOpenFreeVars h (stackOpenFreeVars k (inFreeVars annedFreeVars in_e)) of ((bvs_static', bvs_nonstatic'), fvs') -> (bvs_static', fvs' S.\\ bvs_nonstatic'),
                                                    \h -> case pureHeapOpenFreeVars h (S.empty, S.empty) of ((bvs_static', bvs_nonstatic'), _fvs') -> bvs_static' `S.union` bvs_nonstatic')
  where
    pureHeapOpenFreeVars :: PureHeap -> (BoundVars, FreeVars) -> ((BoundVars, BoundVars), FreeVars)
    pureHeapOpenFreeVars h (bvs, fvs) = (\f -> M.foldrWithKey f ((S.empty, bvs), fvs) h) $ \x' hb ((bvs_static, bvs_nonstatic), fvs) -> case hb of
        Concrete in_e  -> ((bvs_static,             S.insert x' bvs_nonstatic), fvs `S.union` inFreeVars annedTermFreeVars in_e)
        Unfolding in_v -> ((bvs_static,             bvs_nonstatic),             S.insert x' (fvs `S.union` inFreeVars annedValueFreeVars in_v))
        _              -> ((S.insert x' bvs_static, bvs_nonstatic),             fvs)
    
    stackOpenFreeVars :: Stack -> FreeVars -> (BoundVars, FreeVars)
    stackOpenFreeVars k fvs = (S.unions *** (S.union fvs . S.unions)) . unzip . map (stackFrameOpenFreeVars . tagee) $ k
