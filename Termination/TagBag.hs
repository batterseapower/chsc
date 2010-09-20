module Termination.TagBag (
        -- * The TagBag type
        TagBag
    ) where

import Termination.Terminate

import Evaluator.Syntax

import Utilities

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M


newtype TagBag = TagBag { unTagBag :: IM.IntMap Int }
               deriving (Eq)

instance Pretty TagBag where
    pPrint (TagBag m) = braces $ hsep $ punctuate (text ",") [pPrint tg | (tg, count) <- IM.toList m, _ <- replicate count ()]

instance TagCollection TagBag where
    -- NB: this is inverted compared to Neil's definitions (to make it a better match for w.q.o theory)
    tb1 <| tb2 = do
        -- traceRender ("<|", tb1, tb2, tb1 `setEqual` tb2, cardinality tb1, cardinality tb2) $
        guard $ tb1 `setEqual` tb2 && cardinality tb1 <= cardinality tb2
        let growing = IM.keysSet (IM.filter (/= 0) (IM.mapMaybe id (combineIntMaps (const Nothing) Just (\i1 i2 -> Just (i2 - i1)) (unTagBag tb1) (unTagBag tb2))))
        return $ Generaliser {
            generaliseStackFrame  = \kf       -> any (`IS.member` growing) (stackFrameTags' kf),
            generaliseHeapBinding = \_ (_, e) -> pureHeapBindingTag' e `IS.member` growing
          }
    
    stateTags (Heap h _, k, (_, e)) = traceRender ("stateTags (TagBag)", M.map (pureHeapBindingTag' . snd) h, map stackFrameTags' k, focusedTermTag' e) $
                                      pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` tagTagBag (focusedTermTag' e)
      where
        pureHeapTagBag :: PureHeap -> TagBag
        pureHeapTagBag = plusTagBags . map (tagTagBag . pureHeapBindingTag' . snd) . M.elems

        stackTagBag :: Stack -> TagBag
        stackTagBag = mkTagBag . concatMap stackFrameTags'

        tagTagBag :: Tag -> TagBag
        tagTagBag = mkTagBag . return


pureHeapBindingTag' :: AnnedTerm -> Tag
pureHeapBindingTag' = injectTag 5 . annedTag

stackFrameTags' :: StackFrame -> [Tag]
stackFrameTags' = map (injectTag 3) . stackFrameTags

focusedTermTag' :: AnnedTerm -> Tag
focusedTermTag' = injectTag 2 . annedTag


mkTagBag :: [Tag] -> TagBag
mkTagBag = TagBag . IM.unionsWith (+) . map (`IM.singleton` 1)

-- tagBagToList :: TagBag -> [Tag]
-- tagBagToList = IM.foldWithKey (\tg n rest -> replicate n tg ++ rest) [] . unTagBag

plusTagBag :: TagBag -> TagBag -> TagBag
plusTagBag (TagBag tb1) (TagBag tb2) = TagBag (IM.unionWith (+) tb1 tb2)

plusTagBags :: [TagBag] -> TagBag
plusTagBags = TagBag . IM.unionsWith (+) . map unTagBag

cardinality :: TagBag -> Int
cardinality = IM.fold (+) 0 . unTagBag

setEqual :: TagBag -> TagBag -> Bool
setEqual tb1 tb2  = IM.keysSet (unTagBag tb1) == IM.keysSet (unTagBag tb2)
