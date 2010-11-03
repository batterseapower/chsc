{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Evaluator.FreeVars (
    WhyLive(..), Liveness, livenessAllFreeVars,
    mkConcreteLiveness, mkPhantomLiveness, emptyLiveness, plusLiveness, plusLivenesses, whyLive, keepAlive,

    inFreeVars,
    heapBindingLiveness, pureHeapOpenLiveness,
    stackFreeVars, stackFrameFreeVars,
    stateFreeVars, stateStaticFreeVars
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

instance JoinSemiLattice WhyLive where
    ConcreteLive `join` _            = ConcreteLive
    _            `join` ConcreteLive = ConcreteLive
    _            `join` _            = PhantomLive

instance BoundedJoinSemiLattice WhyLive where
    bottom = PhantomLive

newtype Liveness = Liveness { unLiveness :: M.Map (Out Var) WhyLive }
                 deriving (JoinSemiLattice, BoundedJoinSemiLattice)

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

keepAlive :: Maybe WhyLive -> Out Var -> In AnnedTerm -> PureHeap -> PureHeap
keepAlive Nothing             _  _    h = h
keepAlive (Just PhantomLive)  x' in_e h = M.insert x' (Phantom in_e) h
keepAlive (Just ConcreteLive) x' in_e h = M.insert x' (Concrete in_e) h


inFreeVars :: (a -> FreeVars) -> In a -> FreeVars
inFreeVars thing_fvs (rn, thing) = renameFreeVars rn (thing_fvs thing)

heapBindingLiveness :: HeapBinding -> Liveness
heapBindingLiveness Environmental   = emptyLiveness
heapBindingLiveness (Updated _ fvs) = mkPhantomLiveness fvs
heapBindingLiveness (Phantom in_e)  = mkPhantomLiveness  (inFreeVars annedTermFreeVars in_e)
heapBindingLiveness (Concrete in_e) = mkConcreteLiveness (inFreeVars annedTermFreeVars in_e)

pureHeapOpenLiveness :: PureHeap -> (BoundVars, FreeVars) -> (BoundVars, Liveness)
pureHeapOpenLiveness h (bvs, fvs) = M.foldWithKey (\x' hb (bvs, fvs) -> (S.insert x' bvs, fvs `plusLiveness` heapBindingLiveness hb)) (bvs, mkConcreteLiveness fvs) h

pureHeapFreeVars :: PureHeap -> (BoundVars, FreeVars) -> FreeVars
pureHeapFreeVars h (bvs, fvs) = fvs' S.\\ bvs_static' S.\\ bvs_nonstatic'
  where ((bvs_static', bvs_nonstatic'), fvs') = pureHeapOpenFreeVars h (bvs, fvs)

pureHeapOpenFreeVars :: PureHeap -> (BoundVars, FreeVars) -> ((BoundVars, BoundVars), FreeVars)
pureHeapOpenFreeVars h (bvs, fvs) = M.foldWithKey (\x' hb ((bvs_static, bvs_nonstatic), fvs) -> case hb of Concrete in_e -> ((bvs_static, S.insert x' bvs_nonstatic), fvs `S.union` inFreeVars annedTermFreeVars in_e); _ -> ((S.insert x' bvs_static, bvs_nonstatic), fvs)) ((S.empty, bvs), fvs) h

stackFreeVars :: Stack -> FreeVars -> (BoundVars, FreeVars)
stackFreeVars k fvs = (S.unions *** (S.union fvs . S.unions)) . unzip . map stackFrameFreeVars $ k

stackFrameFreeVars :: StackFrame -> (BoundVars, FreeVars)
stackFrameFreeVars kf = case kf of
    Apply x'                -> (S.empty, annedFreeVars x')
    Scrutinise in_alts      -> (S.empty, inFreeVars annedAltsFreeVars in_alts)
    PrimApply _ in_vs in_es -> (S.empty, S.unions (map (inFreeVars annedValueFreeVars) in_vs) `S.union` S.unions (map (inFreeVars annedTermFreeVars) in_es))
    Update x'               -> (S.singleton (annee x'), S.empty)

stateFreeVars :: State -> FreeVars
stateFreeVars (Heap h _, k, in_e) = pureHeapFreeVars h (stackFreeVars k (inFreeVars annedTermFreeVars in_e))

stateStaticFreeVars :: State -> (BoundVars, FreeVars)
stateStaticFreeVars (Heap h _, k, in_e) = (bvs_static', fvs' S.\\ bvs_nonstatic')
  where ((bvs_static', bvs_nonstatic'), fvs') = pureHeapOpenFreeVars h (stackFreeVars k (inFreeVars annedTermFreeVars in_e))
