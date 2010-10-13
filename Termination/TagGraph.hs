{-# LANGUAGE ViewPatterns #-}
module Termination.TagGraph (
        embedWithTagGraphs
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.FreeVars
import Evaluator.Syntax

import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S


type TagGraph = TagMap (TagSet, Count)


embedWithTagGraphs :: Embedding State Generaliser
embedWithTagGraphs = comapEmbedding stateTags generaliserFromGrowing $ refineByTags (comapEmbedding consolidate snd (refineChainTags alwaysEmbedded embedTagCounts))
  where
    consolidate :: (Functor f, Foldable.Foldable f) => f (TagSet, Count) -> (TagSet, f Count)
    consolidate (fmap fst &&& fmap snd -> (ims, counts)) = (Foldable.foldr (IM.unionWith (\() () -> ())) IM.empty ims, counts)
    
    stateTags (Heap h _, k, in_e@(_, e)) = -- traceRender ("stateTags (TagGraph)", graph) $
                                           graph
      where
        graph = pureHeapTagGraph h  
                 `plusTagGraph` stackTagGraph [focusedTermTag' e] k
                 `plusTagGraph` mkTermTagGraph (focusedTermTag' e) in_e
        
        pureHeapTagGraph :: PureHeap -> TagGraph
        pureHeapTagGraph h = plusTagGraphs [mkTagGraph [pureHeapBindingTag' e] (inFreeVars annedTermFreeVars in_e) | in_e@(_, e) <- M.elems h]
        
        stackTagGraph :: [Tag] -> Stack -> TagGraph
        stackTagGraph _         []     = emptyTagGraph
        stackTagGraph focus_tgs (kf:k) = emptyTagGraph { edges = IM.fromList [(kf_tg, IS.singleton focus_tg) | kf_tg <- kf_tgs, focus_tg <- focus_tgs] } -- Binding structure of the stack itself (outer frames refer to inner ones)
                                            `plusTagGraph` mkTagGraph kf_tgs (snd (stackFrameFreeVars kf))                                               -- Binding structure of the stack referring to bound names
                                            `plusTagGraph` stackTagGraph kf_tgs k                                                                        -- Recurse to deal with rest of the stack
          where kf_tgs = stackFrameTags' kf
        
        -- Stores the tags associated with any bound name
        referants = M.map (\(_, e) -> IS.singleton (pureHeapBindingTag' e)) h `M.union` M.fromList [(annee x', IS.fromList (stackFrameTags' kf)) | kf@(Update x') <- k]
        
        -- Find the *tags* referred to from the *names* referred to
        referrerEdges referrer_tgs fvs = M.foldWithKey go IM.empty referants
          where go x referant_tgs edges
                  | x `S.notMember` fvs = edges
                  | otherwise           = foldr (\referrer_tg edges -> IM.insertWith IS.union referrer_tg referant_tgs edges) edges referrer_tgs
        
        referrerEdges' referrer_tgs fvs = S.fold go IM.empty fvs
          where go x edges = case M.lookup x referants of
                                Nothing           -> edges
                                Just referant_tgs -> foldr (\referrer_tg edges -> IM.insertWith IS.union referrer_tg referant_tgs edges) edges referrer_tgs
        
        mkTermTagGraph e_tg in_e = mkTagGraph [e_tg] (inFreeVars annedTermFreeVars in_e)
        mkTagGraph e_tgs fvs = IM.fromList  TagGraph { vertices = IM.unionsWith (+) [IM.singleton e_tg 1 | e_tg <- e_tgs], edges = referrerEdges e_tgs fvs }
    
    generaliserFromGrowing growing = Generaliser {
        generaliseStackFrame  = \kf       -> any (`IS.member` growing) (stackFrameTags' kf),
        generaliseHeapBinding = \_ (_, e) -> pureHeapBindingTag' e `IS.member` growing
      }


pureHeapBindingTag' :: AnnedTerm -> Tag
pureHeapBindingTag' = injectTag 5 . annedTag

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

focusedTermTag' :: AnnedTerm -> Tag
focusedTermTag' = injectTag 2 . annedTag


emptyTagGraph :: TagGraph
emptyTagGraph = IM.empty

plusTagGraph :: TagGraph -> TagGraph -> TagGraph
plusTagGraph = IM.unionWith (\(ts1, count1) (ts2, count2) -> (IM.unionWith (\() () -> ()) ts1 ts1, count1 + count2))

plusTagGraphs :: [TagGraph] -> TagGraph
plusTagGraphs = foldr plusTagGraphs emptyTagGraph
