module Termination.Terminate where

import StaticFlags
import Utilities

import qualified Data.Map as M


newtype TagBag = TagBag { unTagBag :: M.Map Tag Int }
               deriving (Eq)

instance Pretty TagBag where
    pPrint (TagBag m) = braces $ hsep $ punctuate (text ",") [pPrint n | (n, count) <- M.toList m, _ <- replicate count n]

mkTagBag :: [Tag] -> TagBag
mkTagBag = TagBag . M.unionsWith (+) . map (flip M.singleton 1)

plusTagBag :: TagBag -> TagBag -> TagBag
plusTagBag (TagBag tb1) (TagBag tb2) = TagBag (M.unionWith (+) tb1 tb2)

plusTagBags :: [TagBag] -> TagBag
plusTagBags = TagBag . M.unionsWith (+) . map unTagBag

cardinality :: TagBag -> Int
cardinality = M.fold (+) 0 . unTagBag

setEqual :: TagBag -> TagBag -> Bool
setEqual tb1 tb2  = M.keysSet (unTagBag tb1) == M.keysSet (unTagBag tb2)

-- NB: this is inverted compared to Neil's definitions (to make it a better match for w.q.o theory)
(<|) :: TagBag -> TagBag -> Bool
tb1 <| tb2 = -- traceRender ("<|", tb1, tb2, tb1 `setEqual` tb2, cardinality tb1, cardinality tb2) $
             tb1 `setEqual` tb2 && cardinality tb1 <= cardinality tb2


type History = [TagBag]

emptyHistory :: History
emptyHistory = []

data TermRes = Stop | Continue History

terminate :: History -> TagBag -> TermRes
terminate hist here
  -- | traceRender (length hist, tagBag here) && False = undefined
  | tERMINATION_CHECK && any (\prev -> if prev <| here then traceRender (hang (text "terminate") 2 (pPrint hist $$ pPrint here)) True else False) hist
  = Stop
  | otherwise
  = Continue (here : hist)
