module Termination.TagBag (
        embedWithTagBags
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.Syntax

import Utilities

import qualified Data.IntMap as IM
import qualified Data.Map as M


type TagBag = TagMap Count

embedWithTagBags :: Embedding State Generaliser
embedWithTagBags = comapEmbedding stateTags generaliserFromGrowing $ refineByTags embedTagCounts
  where
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagBag)", M.map (pureHeapBindingTag' . snd) h, map stackFrameTags' k, focusedTermTag' e) $
                                      pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` tagTagBag (focusedTermTag' e)
      where
        pureHeapTagBag :: PureHeap -> TagBag
        pureHeapTagBag = plusTagBags . map (tagTagBag . pureHeapBindingTag' . snd) . M.elems
     
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
    
    generaliserFromGrowing growing = Generaliser {
        generaliseStackFrame  = \kf       -> any (`IM.member` growing) (stackFrameTags' kf),
        generaliseHeapBinding = \_ (_, e) -> pureHeapBindingTag' e `IM.member` growing
      }


pureHeapBindingTag' :: AnnedTerm -> Tag
pureHeapBindingTag' = injectTag 5 . annedTag

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

focusedTermTag' :: AnnedTerm -> Tag
focusedTermTag' = injectTag 2 . annedTag
