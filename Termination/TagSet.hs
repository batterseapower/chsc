module Termination.TagSet (
        -- * The TagSet type
        TagSet
    ) where

import Termination.TagBag
import Termination.Terminate

import Evaluator.Syntax

import Utilities

import qualified Data.IntSet as IS
import qualified Data.Map as M


newtype TagSet = TagSet { unTagSet :: IS.IntSet }
               deriving (Eq)

instance Pretty TagSet where
    pPrint (TagSet m) = braces $ hsep $ punctuate (text ",") [pPrint tg | tg <- IS.toList m]

instance TagCollection TagSet where
    (<|) = (==)
    
    growingTags _ _ = IS.empty
    
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagSet)", M.map (pureHeapBindingTag' . snd) h, map stackFrameTags' k, focusedTermTag' e) $
                                      TagSet $ pureHeapTagSet h `IS.union` stackTagSet k `IS.union` tagTagSet (focusedTermTag' e)
      where
        pureHeapTagSet :: PureHeap -> IS.IntSet
        pureHeapTagSet = IS.unions . map (IS.singleton . pureHeapBindingTag' . snd) . M.elems

        stackTagSet :: Stack -> IS.IntSet
        stackTagSet = IS.fromList . concatMap stackFrameTags'

        tagTagSet :: Tag -> IS.IntSet
        tagTagSet = IS.singleton
