module Termination.TagSet (
        embedWithTagSets
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.Syntax

import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M


embedWithTagSets :: WQO State Generaliser
embedWithTagSets = precomp stateTags $ postcomp (const generaliseNothing) equal
  where
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagSet)", M.map heapBindingTagSet h, map stackFrameTags' k, qaTag' e) $
                                      pureHeapTagSet h `IS.union` stackTagSet k `IS.union` tagTagSet (qaTag' e)
      where
        heapBindingTagSet :: HeapBinding -> TagSet
        heapBindingTagSet = maybe IS.empty (tagTagSet . pureHeapBindingTag') . heapBindingTag_
        
        pureHeapTagSet :: PureHeap -> IS.IntSet
        pureHeapTagSet = IS.unions . map heapBindingTagSet . M.elems
    
        stackTagSet :: Stack -> IS.IntSet
        stackTagSet = IS.fromList . concatMap stackFrameTags'
    
        tagTagSet :: Tag -> IS.IntSet
        tagTagSet = IS.singleton


pureHeapBindingTag' :: Tag -> Tag
pureHeapBindingTag' = injectTag 5

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

qaTag' :: Anned QA -> Tag
qaTag' = injectTag 2 . annedTag
