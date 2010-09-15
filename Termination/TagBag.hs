module Termination.TagBag (
        -- * TagBag construction
        TagBag, mkTagBag, plusTagBag, plusTagBags
    ) where

import Utilities

import Termination.Terminate

import qualified Data.IntMap as IM


newtype TagBag = TagBag { unTagBag :: IM.IntMap Int }
               deriving (Eq)

instance Pretty TagBag where
    pPrint (TagBag m) = braces $ hsep $ punctuate (text ",") [pPrint n | (n, count) <- IM.toList m, _ <- replicate count n]

instance TagCollection TagBag where
    -- NB: this is inverted compared to Neil's definitions (to make it a better match for w.q.o theory)
    tb1 <| tb2 = -- traceRender ("<|", tb1, tb2, tb1 `setEqual` tb2, cardinality tb1, cardinality tb2) $
                 tb1 `setEqual` tb2 && cardinality tb1 <= cardinality tb2
    
    growingTags (TagBag tb1) (TagBag tb2) = IM.keysSet (IM.filter (/= 0) (IM.mapMaybe id (combineIntMaps (const Nothing) Just (\i1 i2 -> Just (i2 - i1)) tb1 tb2)))


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
