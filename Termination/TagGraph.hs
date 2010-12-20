{-# LANGUAGE ViewPatterns #-}
module Termination.TagGraph (
        embedWithTagGraphs
    ) where

import Core.FreeVars (FreeVars)
import Core.Renaming (In, Out)
import Core.Syntax (Var)

import Termination.Terminate
import Termination.Generaliser

import Evaluator.FreeVars
import Evaluator.Syntax

import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S


type TagGraph = M.Map TagSet (S.Set TagSet, Nat)


embedWithTagGraphs :: WQO State Generaliser
embedWithTagGraphs = precomp stateTags $ postcomp generaliserFromGrowing $ refineCollection (\discard -> postcomp discard $ zippable (postcomp snd (prod equal nat))) -- NB: NOT using natsWeak
  where
    -- consolidate :: (Functor f, Foldable.Foldable f) => f (TagSet, Nat) -> (TagSet, f Nat)
    --     consolidate (fmap fst &&& fmap snd -> (ims, counts)) = (Foldable.foldr (M.unionWith (\() () -> ())) M.empty ims, counts)
    
    stateTags (Heap h _, k, in_e@(_, e)) = -- traceRender ("stateTags (TagGraph)", graph) $
                                           graph
      where
        graph = pureHeapTagGraph h  
                 `plusTagGraph` stackTagGraph [focusedTermTag' e] k
                 `plusTagGraph` mkTermTagGraph (focusedTermTag' e) in_e
        
        heapBindingTagGraph :: HeapBinding -> TagGraph
        heapBindingTagGraph hb = maybe (mkTagGraph [] S.empty) (\tg -> mkTagGraph [pureHeapBindingTag' tg] (livenessAllFreeVars (heapBindingLiveness hb))) $ heapBindingTag hb
        
        pureHeapTagGraph :: PureHeap -> TagGraph
        pureHeapTagGraph h = plusTagGraphs $ map heapBindingTagGraph (M.elems h)
        
        stackTagGraph :: [TagSet] -> Stack -> TagGraph
        stackTagGraph _         []     = emptyTagGraph
        stackTagGraph focus_tgs (kf:k) = M.fromList [(kf_tg, (S.singleton focus_tg, 0)) | kf_tg <- kf_tgs, focus_tg <- focus_tgs] -- Binding structure of the stack itself (outer frames refer to inner ones)
                                            `plusTagGraph` mkTagGraph kf_tgs (stackFrameBoundVars kf)                               -- Binding structure of the stack referring to bound names
                                            `plusTagGraph` stackTagGraph kf_tgs k                                                   -- Recurse to deal with rest of the stack
          where kf_tgs = stackFrameTags' kf
        
        -- Stores the tags associated with any bound name
        referants :: M.Map (Out Var) (S.Set TagSet)
        referants = M.map (maybe S.empty (S.singleton . pureHeapBindingTag') . heapBindingTag) h `M.union` M.fromList [(annee x', S.fromList (stackFrameTags' kf)) | kf@(Update x') <- k]
        
        -- Find the *tags* referred to from the *names* referred to
        referrerEdges :: [TagSet] -> FreeVars -> TagGraph
        referrerEdges referrer_tgs fvs = M.foldWithKey go M.empty referants
          where go x referant_tgs edges
                  | x `S.notMember` fvs = edges
                  | otherwise           = foldr (\referrer_tg edges -> M.singleton referrer_tg (referant_tgs, 0) `plusTagGraph` edges) edges referrer_tgs
        
        mkTermTagGraph :: TagSet -> In AnnedTerm -> TagGraph
        mkTermTagGraph e_tg in_e = mkTagGraph [e_tg] (inFreeVars annedTermFreeVars in_e)
        
        mkTagGraph :: [TagSet] -> FreeVars -> TagGraph
        mkTagGraph e_tgs fvs = plusTagGraphs [M.singleton e_tg (S.empty, 1) | e_tg <- e_tgs] `plusTagGraph` referrerEdges e_tgs fvs
    
    generaliserFromGrowing :: M.Map TagSet Bool -> Generaliser
    generaliserFromGrowing growing = Generaliser {
          generaliseStackFrame  = \kf   -> any strictly_growing (stackFrameTags' kf),
          generaliseHeapBinding = \_ hb -> maybe False (strictly_growing . pureHeapBindingTag') (heapBindingTag hb)
        }  
      where strictly_growing tg = M.findWithDefault False tg growing


pureHeapBindingTag' :: TagSet -> TagSet
pureHeapBindingTag' = IS.map (injectTag 5)

stackFrameTags' :: StackFrame -> [TagSet]
stackFrameTags' = map (IS.map (injectTag 3)) . stackFrameTags

focusedTermTag' :: AnnedTerm -> TagSet
focusedTermTag' = IS.map (injectTag 2) . annedTag


emptyTagGraph :: TagGraph
emptyTagGraph = M.empty

plusTagGraph :: TagGraph -> TagGraph -> TagGraph
plusTagGraph = M.unionWith (\(tm1, count1) (tm2, count2) -> (tm1 `S.union` tm2, count1 + count2))

plusTagGraphs :: [TagGraph] -> TagGraph
plusTagGraphs = foldr plusTagGraph emptyTagGraph
