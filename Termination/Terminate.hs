{-# LANGUAGE PatternGuards #-}
module Termination.Terminate (
        -- * TagBag construction
        TagBag, mkTagBag, plusTagBag, plusTagBags,

        -- * The termination criterion
        History, TermRes(..), emptyHistory, terminate
    ) where

import StaticFlags
import Utilities

import qualified Data.IntMap as IM


newtype TagBag = TagBag { unTagBag :: IM.IntMap Int }
               deriving (Eq)

instance Pretty TagBag where
    pPrint (TagBag m) = braces $ hsep $ punctuate (text ",") [pPrint n | (n, count) <- IM.toList m, _ <- replicate count n]

mkTagBag :: [Tag] -> TagBag
mkTagBag = TagBag . IM.unionsWith (+) . map (`IM.singleton` 1)

plusTagBag :: TagBag -> TagBag -> TagBag
plusTagBag (TagBag tb1) (TagBag tb2) = TagBag (IM.unionWith (+) tb1 tb2)

plusTagBags :: [TagBag] -> TagBag
plusTagBags = TagBag . IM.unionsWith (+) . map unTagBag

cardinality :: TagBag -> Int
cardinality = IM.fold (+) 0 . unTagBag

setEqual :: TagBag -> TagBag -> Bool
setEqual tb1 tb2  = IM.keysSet (unTagBag tb1) == IM.keysSet (unTagBag tb2)

-- NB: this is inverted compared to Neil's definitions (to make it a better match for w.q.o theory)
(<|) :: TagBag -> TagBag -> Bool
tb1 <| tb2 = -- traceRender ("<|", tb1, tb2, tb1 `setEqual` tb2, cardinality tb1, cardinality tb2) $
             tb1 `setEqual` tb2 && cardinality tb1 <= cardinality tb2


type History a = [(TagBag, a)]

emptyHistory :: History a
emptyHistory = []

data TermRes a = Stop a | Continue (History a)

terminate :: History a -> TagBag -> a -> TermRes a
terminate hist here here_extra
  -- | traceRender (length hist, tagBag here) && False = undefined
  | tERMINATION_CHECK
  , prev_extra:_ <- [prev_extra | (prev, prev_extra) <- hist, if prev <| here then {- traceRender (hang (text "terminate") 2 (pPrint hist $$ pPrint here)) -} True else False]
  = Stop prev_extra
  | otherwise
  = Continue ((here, here_extra) : hist)

