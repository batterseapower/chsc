{-# LANGUAGE BangPatterns, TupleSections, Rank2Types #-}
module Evaluator.Deeds where

import Evaluator.Syntax

import Core.Renaming (In)

import StaticFlags
import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IM
import qualified Data.Map as M
import Data.Tree
import Data.Ord (comparing)


-- | Number of unclaimed deeds. Invariant: always greater than or equal to 0
type Unclaimed = Int

-- | A deed supply shared amongst all expressions
type Deeds = Int

claimDeed :: Deeds -> Anned a -> Maybe Deeds
claimDeed deeds x = claimDeeds deeds x 1

-- NB: it is OK if the number of deeds to claim is negative -- that just causes some deeds to be released
claimDeeds :: Deeds -> Anned a -> Int -> Maybe Deeds
claimDeeds deeds _ _ | not dEEDS = Just deeds
claimDeeds deeds x duplicates = guard (deeds >= want) >> return (deeds - want)
  where want = annedSize x * duplicates

releaseDeedDeep :: Deeds -> Anned a -> Deeds
releaseDeedDeep deeds x = deeds + annedSize x

-- NB: this function relies on the invariant that (annedSize x - thingSize' (annee x) == 1)
releaseDeedDescend :: Deeds -> Anned a -> Deeds
releaseDeedDescend deeds x = deeds - 1


-- | Splits up a number evenly across several partitions in proportions to weights given to those partitions.
--
-- > sum (apportion n weights) == n
apportion :: Deeds -> [Deeds] -> [Deeds]
apportion _      []        = error "apportion: empty list"
apportion orig_n weighting = result
  where
    fracs :: [Rational]
    fracs = assertRender (text "apportion: must have at least one non-zero weight") (denominator /= 0) $
            map (\numerator -> fromIntegral numerator / denominator) weighting
      where denominator = fromIntegral (sum weighting)
    
    -- Here is the idea:
    --  1) Do one pass through the list of fractians
    --  2) Start by allocating the floor of the number of "n" that we should allocate to this weight of the fraction
    --  3) Accumulate the fractional pieces and the indexes that generated them
    --  4) Use circular programming to feed the list of fractional pieces that we actually allowed the allocation
    --     of back in to the one pass we are doing over the list
    ((_, remaining, final_deserving), result) = mapAccumL go (0 :: Int, orig_n, []) fracs
    go (i, n, deserving) frac = ((i + 1, n - whole, (i, remainder) : deserving),
                                 whole + if i `elem` final_deserving_allowed then 1 else 0)
      where (whole, remainder) = properFraction (frac * fromIntegral orig_n)
    
    -- We should prefer to allocate pieces to those bits of the fraction where the error (i.e. the fractional part) is greatest.
    -- We cannot allocate more of these "fixup" pieces than we had "n" left at the end of the first pass.
    final_deserving_allowed = map fst (take remaining (sortBy (comparing (Down . snd)) final_deserving))

noChange, noGain :: Deeds -> Deeds -> Bool
noChange = (==)
noGain = (>=)


-- | Puts any unclaimed deeds in the first argument into the unclaimed deed store of the second argument
releaseDeedsTo :: Deeds -> Deeds -> Deeds
releaseDeedsTo deeds_release deeds_to = deeds_to + deeds_release

-- | Returned 'Deeds' are the identity element of 'releaseDeedsTo'
--
-- mkEmptyDeeds deeds `releaseDeedsTo` deeds == deeds
-- deeds `releaseDeedsTo` mkEmptyDeeds deeds == deeds
emptyDeeds :: Deeds
emptyDeeds = 0


releaseHeapBindingDeeds :: Deeds -> HeapBinding -> Deeds
releaseHeapBindingDeeds deeds = heapBindingHasDeeds (maybe deeds (releaseDeedDeep deeds))

releasePureHeapDeeds :: Deeds -> PureHeap -> Deeds
releasePureHeapDeeds = M.fold (flip releaseHeapBindingDeeds)

releaseStateDeed :: Deeds -> (Heap, Stack, In (Anned a)) -> Deeds
releaseStateDeed deeds (Heap h _, k, (_, e))
  = foldl' (\deeds kf -> releaseDeedDeep deeds (stackFrameSize (tagee kf)))
           (releasePureHeapDeeds (releaseDeedDeep deeds e) h)
           k
