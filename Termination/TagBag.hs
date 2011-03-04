{-# LANGUAGE Rank2Types #-}
module Termination.TagBag (
        embedWithTagBags,
        embedWithTagBagsStrong,
        embedWithTagBagsStrongest
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.FreeVars
import Evaluator.Syntax

import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable
import qualified Data.IntMap as IM
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Graph.Wrapper as G


type TagBag = FinMap Nat

embedWithTagBags, embedWithTagBagsStrong, embedWithTagBagsStrongest :: WQO State Generaliser
embedWithTagBags = embedWithTagBags' natsWeak
embedWithTagBagsStrong = embedWithTagBags' (zippable nat)
embedWithTagBagsStrongest = precomp (id &&& statePartitioning) $ postcomp fst $ prod (embedWithTagBags' (zippable nat)) equal
  where
    statePartitioning :: State -> S.Set (S.Set Fin)
    statePartitioning (_, Heap h _, k, (_, qa)) = result
      where
        -- All of the variables referenced by a particular tag
        tag_references = IM.unionsWith S.union $ [IM.singleton (unFin (tagFin (annedTag e))) (inFreeVars annedTermFreeVars in_e) | hb <- M.elems h, Just in_e@(_, e) <- [heapBindingTerm hb]] ++
                                                 [IM.singleton (unFin (tagFin (tag kf))) (stackFrameFreeVars (tagee kf)) | kf <- k] ++
                                                 [IM.singleton (unFin (tagFin (annedTag qa))) (annedTermFreeVars' (qaToAnnedTerm' (annee qa)))]
        
        -- Inverting the above mapping, all the tags that reference a particular variable
        referencing_tags = M.unionsWith S.union [M.singleton x (S.singleton i) | (i, xs) <- IM.toList tag_references, x <- S.toList xs]
        
        -- Those variables with no attached information
        xs_no_infos = M.keysSet $ M.filter (\hb -> isNothing (heapBindingTerm hb)) h
        
        -- Use graphs to compute groups of tags that refer to overlapping sets of xs_no_infos
        sccs = G.stronglyConnectedComponents $ G.fromListSimple [(Fin tg, [Fin other_tg | x <- S.toList (xs `S.intersection` xs_no_infos), Just other_tgs <- [M.lookup x referencing_tags], other_tg <- S.elems other_tgs]) | (tg, xs) <- IM.toList tag_references]
        
        -- Turn those SCCs into simple sets
        result = S.fromList [S.fromList (Foldable.toList scc) | scc <- sccs]
    
    

embedWithTagBags' :: (forall f. (Foldable.Foldable f, Traversable.Traversable f, Zippable f) => WQO (f Nat) (f Bool))
                  -> WQO State Generaliser
embedWithTagBags' nats = precomp stateTags $ postcomp generaliserFromGrowing $ refineCollection (\discard -> postcomp discard nats)
  where
    stateTags :: State -> TagBag
    stateTags (_, Heap h _, k, (_, qa)) = -- traceRender ("stateTags (TagBag)", M.map heapBindingTagBag h, map stackFrameTag' k, qaTag' qa) $
                                          -- traceRender ("stateTags:heap (TagBag)", M.map heapBindingTag h) $
                                          (\res -> traceRender ("stateTags (TagBag)", res) res) $
                                          pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` tagTagBag (qaTag' qa)
      where
        heapBindingTagBag :: HeapBinding -> TagBag
        heapBindingTagBag = maybe (mkTagBag []) (tagTagBag . pureHeapBindingTag') . heapBindingTag
          
        pureHeapTagBag :: PureHeap -> TagBag
        pureHeapTagBag = plusTagBags . map heapBindingTagBag . M.elems
     
        stackTagBag :: Stack -> TagBag
        stackTagBag = mkTagBag . map stackFrameTag'
     
        tagTagBag :: Tag -> TagBag
        tagTagBag = mkTagBag . return
        
        mkTagBag :: [Tag] -> TagBag
        mkTagBag = plusTagBags . map (\(TG i occs) -> IM.singleton (unFin i) occs)
        
        plusTagBag :: TagBag -> TagBag -> TagBag
        plusTagBag = IM.unionWith (+)
        
        plusTagBags :: [TagBag] -> TagBag
        plusTagBags = foldr plusTagBag IM.empty
    
    generaliserFromGrowing :: FinMap Bool -> Generaliser
    generaliserFromGrowing growing = Generaliser {
          generaliseStackFrame  = \kf   -> strictly_growing (stackFrameTag' kf),
          generaliseHeapBinding = \_ hb -> maybe False (strictly_growing . pureHeapBindingTag') $ heapBindingTag hb
        }
      where strictly_growing tg = IM.findWithDefault False (unFin (tagFin tg)) growing


pureHeapBindingTag' :: Tag -> Tag
pureHeapBindingTag' = injectTag 5

stackFrameTag' :: Tagged StackFrame -> Tag
stackFrameTag' = injectTag 3 . tag

qaTag' :: Anned QA -> Tag
qaTag' = injectTag 2 . annedTag
