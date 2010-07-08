{-# LANGUAGE PatternGuards #-}
module Termination.Terminate where

import Core.Syntax
import Core.Renaming (In)

import Evaluator.Syntax

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


type History1 = [TagBag]
type History = (History1, History1, History1)

emptyHistory :: History
emptyHistory = ([], [], [])

data TermRes = Stop | Continue History

terminate :: History -> State -> TermRes
terminate (h_hist, k_hist, e_hist) (h, k, e)
  -- FIXME: decide what exactly makes this safe! I think it's OK because each individual history has a point at which
  -- *any* new entry will cause it to blow the whistle.
  --
  -- NB: each individual history being a quasi order is not sufficient for terminate itself to define a well-quasi-order!
  -- Well-quasi-orderness is not closed under tupling.
  = case (terminate1 h_hist (heapTagBag h),
          terminate1 k_hist (stackTagBag k),
          terminate1 e_hist (inTaggedTermTagBag e)) of
      (Nothing,    Nothing,    Nothing)    -> Stop
      (mb_h_hist', mb_k_hist', mb_e_hist') -> Continue (fromMaybe h_hist mb_h_hist', fromMaybe k_hist mb_k_hist', fromMaybe e_hist mb_e_hist')

terminate1 :: History1 -> TagBag -> Maybe History1
terminate1 hist here
  -- | traceRender (length hist, tagBag here) && False = undefined
  | tERMINATION_CHECK && any (\prev -> if prev <| here then traceRender (hang (text "terminate1") 2 (pPrint hist $$ pPrint here)) True else False) hist
  = Nothing
  | otherwise
  = Just (here : hist)


heapTagBag :: Heap -> TagBag
heapTagBag (Heap h _) = plusTagBags $ map (taggedTagBag . unTaggedTerm . snd) $ M.elems h

stackTagBag :: Stack -> TagBag
stackTagBag = plusTagBags . map taggedTagBag

inTaggedTermTagBag :: In TaggedTerm -> TagBag
inTaggedTermTagBag = taggedTagBag . unTaggedTerm . snd

taggedTagBag :: Tagged a -> TagBag
taggedTagBag = tagTagBag . tag

tagTagBag :: Tag -> TagBag
tagTagBag = mkTagBag . return
