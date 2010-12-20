module Termination.TagSet (
        embedWithTagSets
    ) where

import Termination.Terminate
import Termination.Generaliser

import Evaluator.Syntax

import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S


embedWithTagSets :: WQO State Generaliser
embedWithTagSets = precomp stateTags $ postcomp (const generaliseNothing) equal
  where
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagSet)", M.map heapBindingTagSet h, map stackFrameTags' k, focusedTermTag' e) $
                                      pureHeapTagSet h `S.union` stackTagSet k `S.union` tagTagSet (focusedTermTag' e)
      where
        heapBindingTagSet :: HeapBinding -> S.Set TagSet
        heapBindingTagSet = maybe S.empty (tagTagSet . pureHeapBindingTag') . heapBindingTag
        
        pureHeapTagSet :: PureHeap -> S.Set TagSet
        pureHeapTagSet = S.unions . map heapBindingTagSet . M.elems
    
        stackTagSet :: Stack -> S.Set TagSet
        stackTagSet = S.fromList . concatMap stackFrameTags'
    
        tagTagSet :: TagSet -> S.Set TagSet
        tagTagSet = S.singleton


pureHeapBindingTag' :: TagSet -> TagSet
pureHeapBindingTag' = IS.map (injectTag 5)

stackFrameTags' :: StackFrame -> [TagSet]
stackFrameTags' = map (IS.map (injectTag 3)) . stackFrameTags

focusedTermTag' :: AnnedTerm -> TagSet
focusedTermTag' = IS.map (injectTag 2) . annedTag
