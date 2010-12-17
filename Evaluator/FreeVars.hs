{-# LANGUAGE GeneralizedNewtypeDeriving, PatternGuards #-}
module Evaluator.FreeVars (
    WhyLive(..), Liveness, livenessAllFreeVars,
    mkConcreteLiveness, mkPhantomLiveness, emptyLiveness, plusLiveness, plusLivenesses,
    whyLive,

    inFreeVars,
    heapBindingLiveness,
    pureHeapBoundVars, stackBoundVars, stackFrameBoundVars,
    stateFreeVars, stateStaticBinders, stateStaticBindersAndFreeVars
  ) where

import Core.Syntax
import Evaluator.Syntax

import Core.FreeVars
import Core.Renaming

import Utilities

import Algebra.Lattice

import qualified Data.Map as M
import qualified Data.Set as S


data WhyLive = PhantomLive | ConcreteLive
             deriving (Eq, Show)

instance Pretty WhyLive where
    pPrint = text . show

instance JoinSemiLattice WhyLive where
    ConcreteLive `join` _            = ConcreteLive
    _            `join` ConcreteLive = ConcreteLive
    _            `join` _            = PhantomLive

instance BoundedJoinSemiLattice WhyLive where
    bottom = PhantomLive

newtype Liveness = Liveness { unLiveness :: M.Map (Out Var) WhyLive }
                 deriving (Eq, JoinSemiLattice, BoundedJoinSemiLattice)

mkConcreteLiveness, mkPhantomLiveness :: FreeVars -> Liveness
mkConcreteLiveness fvs = Liveness $ setToMap ConcreteLive fvs
mkPhantomLiveness fvs = Liveness $ setToMap PhantomLive fvs

-- | Warning: you almost never actually want to use this function, since this function also reports free variables of phantoms.
livenessAllFreeVars :: Liveness -> FreeVars
livenessAllFreeVars = M.keysSet . unLiveness

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

heapBindingLiveness :: HeapBinding -> Liveness
heapBindingLiveness Environmental   = emptyLiveness
heapBindingLiveness (Updated _ fvs) = mkPhantomLiveness fvs
heapBindingLiveness (Phantom in_e)  = mkPhantomLiveness  (inFreeVars annedTermFreeVars in_e)
heapBindingLiveness (Concrete in_e) = mkConcreteLiveness (inFreeVars annedTermFreeVars in_e)

pureHeapBoundVars :: PureHeap -> BoundVars
pureHeapBoundVars = M.keysSet . M.filter (not . heapBindingNonConcrete)

stackBoundVars :: Stack -> BoundVars
stackBoundVars = S.unions . map stackFrameBoundVars

stackFrameBoundVars :: StackFrame -> BoundVars
stackFrameBoundVars = fst . stackFrameOpenFreeVars

stackFrameOpenFreeVars :: StackFrame -> (BoundVars, FreeVars)
stackFrameOpenFreeVars kf = case kf of
    Apply x'                -> (S.empty, annedFreeVars x')
    Scrutinise in_alts      -> (S.empty, inFreeVars annedAltsFreeVars in_alts)
    PrimApply _ in_vs in_es -> (S.empty, S.unions (map (inFreeVars annedValueFreeVars) in_vs) `S.union` S.unions (map (inFreeVars annedTermFreeVars) in_es))
    Update x'               -> (S.singleton (annee x'), S.empty)

-- | Returns the free variables that the state would have if it were residualised right now (i.e. variables bound by phantom bindings are in the free vars set)
stateFreeVars :: State -> FreeVars
stateFreeVars = snd . stateStaticBindersAndFreeVars

stateStaticBinders :: State -> BoundVars
stateStaticBinders = fst . stateStaticBindersAndFreeVars

-- | Returns the free variables that the state would have if it were residualised right now (i.e. excludes static binders),
-- along with the static binders as a separate set.
stateStaticBindersAndFreeVars :: State -> (BoundVars, FreeVars)
stateStaticBindersAndFreeVars (Heap h _, k, in_e) = (bvs_static', fvs' S.\\ bvs_nonstatic')
  where
    ((bvs_static', bvs_nonstatic'), fvs') = pureHeapOpenFreeVars h (stackOpenFreeVars k (inFreeVars annedTermFreeVars in_e))
    
    pureHeapOpenFreeVars :: PureHeap -> (BoundVars, FreeVars) -> ((BoundVars, BoundVars), FreeVars)
    pureHeapOpenFreeVars h (bvs, fvs) = M.foldWithKey (\x' hb ((bvs_static, bvs_nonstatic), fvs) -> case hb of Concrete in_e -> ((bvs_static, S.insert x' bvs_nonstatic), fvs `S.union` inFreeVars annedTermFreeVars in_e); _ -> ((S.insert x' bvs_static, bvs_nonstatic), fvs)) ((S.empty, bvs), fvs) h
    
    stackOpenFreeVars :: Stack -> FreeVars -> (BoundVars, FreeVars)
    stackOpenFreeVars k fvs = (S.unions *** (S.union fvs . S.unions)) . unzip . map stackFrameOpenFreeVars $ k
