module Termination.TagBag (
        embedWithTagBags
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.Syntax

import Utilities

import qualified Data.IntMap as IM
import qualified Data.Map as M


type TagBag = TagMap Nat

embedWithTagBags :: WQO State Generaliser
embedWithTagBags = precomp stateTags $ postcomp generaliserFromGrowing $ refineCollection (\discard -> postcomp discard $ natsWeak) -- TODO: have a version where I replace weakManyNat with (zippable nat)
  where
    -- NB: this is stronger than 
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagBag)", M.map heapBindingTagBag h, map stackFrameTags' k, focusedTermTag' e) $
                                      pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` tagTagBag (focusedTermTag' e)
      where
        heapBindingTagBag :: HeapBinding -> TagBag
        heapBindingTagBag = maybe (mkTagBag []) (tagTagBag . pureHeapBindingTag') . heapBindingTag_
          
        pureHeapTagBag :: PureHeap -> TagBag
        pureHeapTagBag = plusTagBags . map heapBindingTagBag . M.elems
     
        stackTagBag :: Stack -> TagBag
        stackTagBag = mkTagBag . concatMap stackFrameTags'
     
        tagTagBag :: Tag -> TagBag
        tagTagBag = mkTagBag . return
        
        mkTagBag :: [Tag] -> TagBag
        mkTagBag = plusTagBags . map (\t -> IM.singleton t 1)
        
        plusTagBag :: TagBag -> TagBag -> TagBag
        plusTagBag = IM.unionWith (+)
        
        plusTagBags :: [TagBag] -> TagBag
        plusTagBags = foldr plusTagBag IM.empty
    
    generaliserFromGrowing :: TagMap Bool -> Generaliser
    generaliserFromGrowing growing = Generaliser {
          generaliseStackFrame  = \kf   -> any strictly_growing (stackFrameTags' kf),
          generaliseHeapBinding = \_ hb -> maybe False (strictly_growing . pureHeapBindingTag') $ heapBindingTag_ hb
        }
      where strictly_growing tg = IM.findWithDefault False tg growing


pureHeapBindingTag' :: Tag -> Tag
pureHeapBindingTag' = injectTag 5

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

focusedTermTag' :: AnnedTerm -> Tag
focusedTermTag' = injectTag 2 . annedTag
