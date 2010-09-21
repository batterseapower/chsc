module Termination.TagSet (
        -- * The TagSet type
        TagSet
    ) where

import Termination.Terminate

import Evaluator.Syntax

import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M


newtype TagSet = TagSet { unTagSet :: IS.IntSet }

instance Pretty TagSet where
    pPrint (TagSet m) = braces $ hsep $ punctuate (text ",") [pPrint tg | tg <- IS.toList m]

instance TagCollection TagSet where
    ts1 <| ts2 = guard (unTagSet ts1 == unTagSet ts2) >> return generaliseNothing
    
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagSet)", M.map (pureHeapBindingTags' . snd) h, map stackFrameTags' k, focusedTermTags' e) $
                                      TagSet $ pureHeapTagSet h `IS.union` stackTagSet k `IS.union` IS.fromList (focusedTermTags' e)
      where
        pureHeapTagSet :: PureHeap -> IS.IntSet
        pureHeapTagSet = IS.unions . map (IS.fromList . pureHeapBindingTags' . snd) . M.elems

        stackTagSet :: Stack -> IS.IntSet
        stackTagSet = IS.fromList . concatMap stackFrameTags'


pureHeapBindingTags' :: AnnedTerm -> [Tag]
pureHeapBindingTags' = map (injectTag 5) . annedTags

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

focusedTermTags' :: AnnedTerm -> [Tag]
focusedTermTags' = map (injectTag 2) . annedTags
