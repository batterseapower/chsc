{-# LANGUAGE ViewPatterns #-}
module Termination.Terminate (
    History,
    emptyHistory,
    
    TermRes(..), 
    isStop, terminate
  ) where

import Core.Syntax
import Evaluator.Syntax

import StaticFlags
import Utilities

import qualified Data.IntMap as IM
import qualified Data.Map as M


newtype TagBag = TagBag { unTagBag :: IM.IntMap Int }
               deriving (Eq)

instance Pretty TagBag where
    pPrint (TagBag m) = braces $ hsep $ punctuate (text ",") [pPrint n | (n, count) <- IM.toList m, _ <- replicate count n]

mkTagBag :: [Tag] -> TagBag
mkTagBag = TagBag . IM.unionsWith (+) . map (flip IM.singleton 1)

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


-- This family of functions is the whole reason that I have to thread Tag information throughout the rest of the code:

stateTagBag :: State -> TagBag
stateTagBag (Heap h _, k, (_, e)) = pureHeapTagBag h `plusTagBag` stackTagBag k `plusTagBag` taggedTermTagBag e

pureHeapTagBag :: PureHeap -> TagBag
pureHeapTagBag = plusTagBags . map (taggedTagBag 5 . snd) . M.elems

stackTagBag :: Stack -> TagBag
stackTagBag = plusTagBags . map (tagTagBag 3) . concatMap stackFrameTags

taggedTermTagBag :: TaggedTerm -> TagBag
taggedTermTagBag = taggedTagBag 2

taggedTagBag :: Int -> Tagged a -> TagBag
taggedTagBag cls = tagTagBag cls . tag

tagTagBag :: Int -> Tag -> TagBag
tagTagBag cls = mkTagBag . return . injectTag cls


data TagBaggedState = TagBaggedState { tagBag :: TagBag, state :: State }

mkTagBaggedState :: State -> TagBaggedState
mkTagBaggedState s = TagBaggedState (stateTagBag s) s


type History = [TagBaggedState]

emptyHistory :: History
emptyHistory = []

data TermRes = Stop State | Continue History

isStop :: TermRes -> Bool
isStop (Stop _) = True
isStop _        = False

terminate :: History -> State -> TermRes
terminate hist (mkTagBaggedState -> here)
  -- | traceRender (length hist, tagBag here) && False = undefined
  | tERMINATION_CHECK
  , prev:_ <- filter (\prev -> if tagBag prev <| tagBag here then {- traceRender (hang (text "terminate") 2 (pPrint hist $$ pPrint here)) -} True else False) hist
  = Stop (state prev)
  | otherwise
  = Continue (here : hist)
