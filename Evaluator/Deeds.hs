{-# LANGUAGE BangPatterns, TupleSections, Rank2Types #-}
module Evaluator.Deeds where

import StaticFlags
import Utilities

import Data.Ord (comparing)


-- | Number of unclaimed deeds. Invariant: always greater than or equal to 0
type Unclaimed = Int

-- | A deed supply shared amongst all expressions
type Deeds = Int

-- NB: it is OK if the number of deeds to claim is negative -- that just causes some deeds to be released
claimDeeds :: Deeds -> Int -> Maybe Deeds
claimDeeds deeds want = guard (not dEEDS || deeds >= want) >> return (deeds - want)


-- | Splits up a number evenly across several partitions in proportions to weights given to those partitions.
--
-- > sum (apportion n weights) == n
--
-- Annoyingly, it is important that this works properly if n is negative as well -- these can occur
-- when we have turned off deed checking. I don't care about handling negative weights.
apportion :: Deeds -> [Deeds] -> [Deeds]
apportion _      []        = error "apportion: empty list"
apportion orig_n weighting
  | orig_n < 0 = map negate $ apportion (negate orig_n) weighting
  | otherwise  = result
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
