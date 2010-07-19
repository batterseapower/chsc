{-# LANGUAGE BangPatterns #-}
module Size.Deeds where

import Utilities

import qualified Data.IntMap as IM
import Data.Tree


-- | Number of unclaimed deeds. Invariant: always greater than or equal to 0
type Unclaimed = Int
newtype Deeds = Deeds { unDeeds :: IM.IntMap ([Tag], Unclaimed) }
-- TODO: could be slightly neater: only need to store Deeds for the *leaves* of the tree, and a mapping that
-- tells us which leaves the node corresponding to any given Tag dominates.

mkDeeds :: Unclaimed -> Tree Tag -> Deeds
mkDeeds k = Deeds . go IM.empty
  where
    go m (Node tg trees) = foldl' go (IM.insert tg (map rootLabel trees, k) m) trees

claimDeed :: Deeds -> Tag -> Maybe Deeds
claimDeed deeds tg = claimDeeds deeds tg 1

-- NB: it is OK if the number of deeds to claim is negative -- that just causes some deeds to be released
claimDeeds :: Deeds -> Tag -> Int -> Maybe Deeds
claimDeeds (Deeds m) tg want = if unclaimed < want then Nothing else foldM claimDeed (Deeds (IM.insert tg (child_tgs, unclaimed - want) m)) child_tgs
  where !(child_tgs, unclaimed) = lookupTag tg m

releaseDeedDeep :: Deeds -> Tag -> Deeds
releaseDeedDeep deeds tg = foldl' releaseDeedDeep deeds' child_tgs
  where (deeds', child_tgs) = releaseDeedDescend deeds tg

releaseDeedDescend :: Deeds -> Tag -> (Deeds, [Tag])
releaseDeedDescend (Deeds m) tg = (Deeds (IM.insert tg (child_tgs, unclaimed + 1) m), child_tgs)
  where !(child_tgs, unclaimed) = lookupTag tg m

releaseDeedDescend_ :: Deeds -> Tag -> Deeds
releaseDeedDescend_ deeds tg = fst (releaseDeedDescend deeds tg)

lookupTag :: Tag -> IM.IntMap ([Tag], Unclaimed) -> ([Tag], Unclaimed)
lookupTag tg m = expectJust "claimDeed: bad Tag" (IM.lookup tg m)
