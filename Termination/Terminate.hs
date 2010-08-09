{-# LANGUAGE PatternGuards #-}
module Termination.Terminate (
        -- * TagBag construction
        TagBag, mkTagBag, plusTagBag, plusTagBags,

        -- * The termination criterion
        History, TermRes(..), emptyHistory, terminate,
        
        -- * History combination for rollback
        forgetFutureHistory
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


newtype History a = History { unHistory :: [(TagBag, a)] }

instance Functor History where
    fmap f hist = History $ map (second f) (unHistory hist)

emptyHistory :: History a
emptyHistory = History []

data TermRes a = Stop a | Continue (History a)

terminate :: History a -> TagBag -> a -> TermRes a
terminate hist here here_extra
  -- | traceRender (length hist, tagBag here) && False = undefined
  | tERMINATION_CHECK
  , prev_extra:_ <- [prev_extra | (prev, prev_extra) <- unHistory hist, if prev <| here then {- traceRender (hang (text "terminate") 2 (pPrint hist $$ pPrint here)) -} True else False]
  = Stop prev_extra
  | otherwise
  = Continue (History $ (here, here_extra) : unHistory hist)

-- FIXME: make less ugly
forgetFutureHistory :: History (Maybe a) -> History (Maybe a) -> History (Maybe a)
forgetFutureHistory (History short) (History long) = History $ short ++ fmap (second (const Nothing)) (short `dropBy` long)
