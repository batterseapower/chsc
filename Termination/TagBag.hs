{-# LANGUAGE Rank2Types #-}
module Termination.TagBag (
        embedWithTagBags,
        embedWithTagBagsStrong
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.Syntax

import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable
import qualified Data.IntMap as IM
import qualified Data.Map as M


type TagBag = FinMap Nat

embedWithTagBags, embedWithTagBagsStrong :: WQO State Generaliser
embedWithTagBags = embedWithTagBags' natsWeak
embedWithTagBagsStrong = embedWithTagBags' (zippable nat)

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
