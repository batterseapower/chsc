{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Evaluator.FreeVars (
    WhyLive(..), Liveness,
    mkConcreteLiveness, mkPhantomLiveness, emptyLiveness, plusLiveness, plusLivenesses, whyLive, keepAlive,

    inFreeVars,
    heapBindingLiveness, heapBindingFreeVars {- FIXME: remove export -}, pureHeapFreeVars, pureHeapOpenFreeVars,
    stackFreeVars, stackFrameFreeVars,
    stateFreeVars
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
heapBindingLiveness (Phantom in_e)  = mkPhantomLiveness  (inFreeVars annedTermFreeVars in_e)
heapBindingLiveness (Concrete in_e) = mkConcreteLiveness (inFreeVars annedTermFreeVars in_e)

heapBindingFreeVars :: HeapBinding -> FreeVars
heapBindingFreeVars = maybe S.empty (inFreeVars annedTermFreeVars) . heapBindingTerm

pureHeapFreeVars :: PureHeap -> (BoundVars, FreeVars) -> FreeVars
pureHeapFreeVars h (bvs, fvs) = fvs' S.\\ bvs'
  where (bvs', fvs') = pureHeapOpenFreeVars h (bvs, fvs)

pureHeapOpenFreeVars :: PureHeap -> (BoundVars, FreeVars) -> (BoundVars, FreeVars)
pureHeapOpenFreeVars = flip $ M.foldWithKey (\x' hb (bvs, fvs) -> (S.insert x' bvs, fvs `S.union` heapBindingFreeVars hb))

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
