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

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S


type TagGraph = TagMap (TagSet, Nat)


embedWithTagGraphs :: WQO State Generaliser
embedWithTagGraphs = precomp stateTags $ postcomp generaliserFromGrowing $ refineCollection (\discard -> postcomp discard $ zippable (postcomp snd (prod equal nat))) -- NB: NOT using natsWeak
  where
    -- consolidate :: (Functor f, Foldable.Foldable f) => f (TagSet, Nat) -> (TagSet, f Nat)
    --     consolidate (fmap fst &&& fmap snd -> (ims, counts)) = (Foldable.foldr (IM.unionWith (\() () -> ())) IM.empty ims, counts)
    
    stateTags (Heap h _, k, in_e@(_, e)) = -- traceRender ("stateTags (TagGraph)", graph) $
                                           graph
      where
        graph = pureHeapTagGraph h  
                 `plusTagGraph` stackTagGraph [focusedTermTag' e] k
                 `plusTagGraph` mkTermTagGraph (focusedTermTag' e) in_e
        
        heapBindingTagGraph :: HeapBinding -> TagGraph
        heapBindingTagGraph hb = maybe (mkTagGraph [] S.empty) (\tg -> mkTagGraph [pureHeapBindingTag' tg] (heapBindingReferences hb)) $ heapBindingTag_ hb
        
        pureHeapTagGraph :: PureHeap -> TagGraph
        pureHeapTagGraph h = plusTagGraphs $ map heapBindingTagGraph (M.elems h)
        
        stackTagGraph :: [Tag] -> Stack -> TagGraph
        stackTagGraph _         []     = emptyTagGraph
        stackTagGraph focus_tgs (kf:k) = IM.fromList [(kf_tg, (IS.singleton focus_tg, 0)) | kf_tg <- kf_tgs, focus_tg <- focus_tgs] -- Binding structure of the stack itself (outer frames refer to inner ones)
                                            `plusTagGraph` mkTagGraph kf_tgs (stackFrameBoundVars kf)                               -- Binding structure of the stack referring to bound names
                                            `plusTagGraph` stackTagGraph kf_tgs k                                                   -- Recurse to deal with rest of the stack
          where kf_tgs = stackFrameTags' kf
        
        -- Stores the tags associated with any bound name
        referants :: M.Map (Out Var) TagSet
        referants = M.map (maybe IS.empty (IS.singleton . pureHeapBindingTag') . heapBindingTag_) h `M.union` M.fromList [(annee x', IS.fromList (stackFrameTags' kf)) | kf@(Update x' _) <- k]
        
        -- Find the *tags* referred to from the *names* referred to
        referrerEdges :: [Tag] -> FreeVars -> TagGraph
        referrerEdges referrer_tgs fvs = M.foldrWithKey go IM.empty referants
          where go x referant_tgs edges
                  | x `S.notMember` fvs = edges
                  | otherwise           = foldr (\referrer_tg edges -> IM.singleton referrer_tg (referant_tgs, 0) `plusTagGraph` edges) edges referrer_tgs
        
        mkTermTagGraph :: Tag -> In AnnedTerm -> TagGraph
        mkTermTagGraph e_tg in_e = mkTagGraph [e_tg] (inFreeVars annedTermFreeVars in_e)
        
        mkTagGraph :: [Tag] -> FreeVars -> TagGraph
        mkTagGraph e_tgs fvs = plusTagGraphs [IM.singleton e_tg (IS.empty, 1) | e_tg <- e_tgs] `plusTagGraph` referrerEdges e_tgs fvs
    
    generaliserFromGrowing :: TagMap Bool -> Generaliser
    generaliserFromGrowing growing = Generaliser {
          generaliseStackFrame  = \kf   -> any strictly_growing (stackFrameTags' kf),
          generaliseHeapBinding = \_ hb -> maybe False (strictly_growing . pureHeapBindingTag') (heapBindingTag_ hb)
        }  
      where strictly_growing tg = IM.findWithDefault False tg growing


pureHeapBindingTag' :: Tag -> Tag
pureHeapBindingTag' = injectTag 5

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

focusedTermTag' :: AnnedTerm -> Tag
focusedTermTag' = injectTag 2 . annedTag


emptyTagGraph :: TagGraph
emptyTagGraph = IM.empty

plusTagGraph :: TagGraph -> TagGraph -> TagGraph
plusTagGraph = IM.unionWith (\(tm1, count1) (tm2, count2) -> (tm1 `IS.union` tm2, count1 + count2))

plusTagGraphs :: [TagGraph] -> TagGraph
plusTagGraphs = foldr plusTagGraph emptyTagGraph
