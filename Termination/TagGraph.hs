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


type TagGraph = FinMap (FinSet, Nat)


embedWithTagGraphs :: WQO State Generaliser
embedWithTagGraphs = precomp stateTags $ postcomp generaliserFromGrowing $ refineCollection (\discard -> postcomp discard $ zippable (postcomp snd (prod equal nat))) -- NB: NOT using natsWeak
  where
    -- consolidate :: (Functor f, Foldable.Foldable f) => f (TagSet, Nat) -> (TagSet, f Nat)
    --     consolidate (fmap fst &&& fmap snd -> (ims, counts)) = (Foldable.foldr (IM.unionWith (\() () -> ())) IM.empty ims, counts)
    
    stateTags :: State -> TagGraph
    stateTags (_, Heap h _, k, in_qa@(_, qa)) = -- traceRender ("stateTags (TagGraph)", graph) $
                                             graph
      where
        graph = pureHeapTagGraph h  
                 `plusTagGraph` stackTagGraph (tagInt (qaTag' qa)) k
                 `plusTagGraph` mkQATagGraph (qaTag' qa) in_qa
        
        heapBindingTagGraph :: HeapBinding -> TagGraph
        heapBindingTagGraph hb = maybe emptyTagGraph (\tg -> mkTagGraph (pureHeapBindingTag' tg) (heapBindingFreeVars hb)) $ heapBindingTag hb
        
        pureHeapTagGraph :: PureHeap -> TagGraph
        pureHeapTagGraph h = plusTagGraphs $ map heapBindingTagGraph (M.elems h)
        
        stackTagGraph :: Int -> Stack -> TagGraph
        stackTagGraph _        []     = emptyTagGraph
        stackTagGraph focus_i (kf:k) = IM.singleton (tagInt kf_tg) (IS.singleton focus_i, 0)  -- Binding structure of the stack itself (outer frames refer to inner ones)
                                          `plusTagGraph` mkTagGraph kf_tg (stackFrameBoundVars (tagee kf))    -- Binding structure of the stack referring to bound names
                                          `plusTagGraph` stackTagGraph (tagInt kf_tg) k                       -- Recurse to deal with rest of the stack
          where kf_tg = stackFrameTag' kf
        
        -- Stores the tags associated with any bound name
        referants :: M.Map (Out Var) FinSet
        referants = M.map (maybe IS.empty (\hb -> IS.singleton (tagInt (pureHeapBindingTag' hb))) . heapBindingTag) h `M.union` M.fromList [(x', IS.singleton (tagInt (stackFrameTag' kf))) | kf@(tagee -> Update x') <- k]
        
        -- Find the *tags* referred to from the *names* referred to
        referrerEdges :: Fin -> FreeVars -> TagGraph
        referrerEdges referrer_i fvs = M.foldrWithKey go IM.empty referants
          where go x referant_tgs edges
                  | x `S.notMember` fvs = edges
                  | otherwise           = IM.singleton (unFin referrer_i) (referant_tgs, 0) `plusTagGraph` edges
        
        mkQATagGraph :: Tag -> In (Anned QA) -> TagGraph
        mkQATagGraph qa_tg in_qa = mkTagGraph qa_tg (inFreeVars annedFreeVars in_qa)
        
        mkTagGraph :: Tag -> FreeVars -> TagGraph
        mkTagGraph (TG e_i e_occs) fvs = IM.singleton (unFin e_i) (IS.empty, e_occs) `plusTagGraph` referrerEdges e_i fvs


emptyTagGraph :: TagGraph
emptyTagGraph = IM.empty

plusTagGraph :: TagGraph -> TagGraph -> TagGraph
plusTagGraph = IM.unionWith (\(tm1, count1) (tm2, count2) -> (tm1 `IS.union` tm2, count1 + count2))

plusTagGraphs :: [TagGraph] -> TagGraph
plusTagGraphs = foldr plusTagGraph emptyTagGraph
