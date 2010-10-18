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
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagSet)", M.map (pureHeapBindingTag' . snd) h, map stackFrameTags' k, focusedTermTag' e) $
                                      pureHeapTagSet h `IS.union` stackTagSet k `IS.union` tagTagSet (focusedTermTag' e)
      where
        pureHeapTagSet :: PureHeap -> IS.IntSet
        pureHeapTagSet = IS.unions . map (IS.singleton . pureHeapBindingTag' . snd) . M.elems
    
        stackTagSet :: Stack -> IS.IntSet
        stackTagSet = IS.fromList . concatMap stackFrameTags'
    
        tagTagSet :: Tag -> IS.IntSet
        tagTagSet = IS.singleton


pureHeapBindingTag' :: AnnedTerm -> Tag
pureHeapBindingTag' = injectTag 5 . annedTag

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

focusedTermTag' :: AnnedTerm -> Tag
focusedTermTag' = injectTag 2 . annedTag
