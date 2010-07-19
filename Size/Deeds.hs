{-# LANGUAGE BangPatterns #-}
module Size.Deeds (
    Unclaimed, Deeds,
    mkDeeds,
    claimDeed, claimDeeds,
    releaseDeedDeep, releaseDeedDescend_
  ) where

import StaticFlags
import Utilities

import qualified Data.IntMap as IM
import Data.Tree


-- | Number of unclaimed deeds. Invariant: always greater than or equal to 0
type Unclaimed = Int
data Deeds = Deeds {
    rootTag :: Tag,
    rebuild :: Tree Unclaimed -> Doc,
    unclaimedMap :: IM.IntMap ([Tag], Unclaimed)
  }
-- TODO: could be slightly neater: only need to store Deeds for the *leaves* of the tree, and a mapping that
-- tells us which leaves the node corresponding to any given Tag dominates.

instance Pretty Deeds where
    pPrint deeds = rebuild deeds (reifyDeedsTree deeds)

-- NB: the correctness of this function depends on the Tags in the input all being distinct
reifyDeedsTree :: Deeds -> Tree Unclaimed
reifyDeedsTree deeds = go (rootTag deeds)
  where
    go :: Tag -> Tree Unclaimed
    go tg = Node unclaimed (map go child_tgs)
      where !(child_tgs, unclaimed) = lookupTag tg (unclaimedMap deeds)


mkDeeds :: Unclaimed -> (Tree Tag, Tree Tag -> Doc) -> Deeds
mkDeeds k (t@(Node root_tg _), rb) = -- traceRender ("mkDeeds", fmap (const (1 :: Int)) t, fmap (const (1 :: Int)) (reifyDeedsTree deeds), rb (fmap (const (1 :: Int)) (reifyDeedsTree deeds))) $
                                     deeds
  where
    deeds = Deeds root_tg rb (go IM.empty t)
    go m (Node tg trees) = foldl' go (IM.insert tg (map rootLabel trees, k) m) trees

claimDeed :: Deeds -> Tag -> Maybe Deeds
claimDeed deeds tg = claimDeeds deeds tg 1

-- NB: it is OK if the number of deeds to claim is negative -- that just causes some deeds to be released
claimDeeds :: Deeds -> Tag -> Int -> Maybe Deeds
claimDeeds deeds tg want = if gENERALISATION && (unclaimed < want) then Nothing else foldM claimDeed (deeds { unclaimedMap = IM.insert tg (child_tgs, unclaimed - want) (unclaimedMap deeds) }) child_tgs
  where !(child_tgs, unclaimed) = lookupTag tg (unclaimedMap deeds)

releaseDeedDeep :: Deeds -> Tag -> Deeds
releaseDeedDeep deeds tg = foldl' releaseDeedDeep deeds' child_tgs
  where (deeds', child_tgs) = releaseDeedDescend deeds tg

releaseDeedDescend :: Deeds -> Tag -> (Deeds, [Tag])
releaseDeedDescend deeds tg = (deeds { unclaimedMap = IM.insert tg (child_tgs, unclaimed + 1) (unclaimedMap deeds) }, child_tgs)
  where !(child_tgs, unclaimed) = lookupTag tg (unclaimedMap deeds)

releaseDeedDescend_ :: Deeds -> Tag -> Deeds
releaseDeedDescend_ deeds tg = fst (releaseDeedDescend deeds tg)

lookupTag :: Tag -> IM.IntMap ([Tag], Unclaimed) -> ([Tag], Unclaimed)
lookupTag tg m = expectJust "lookupTag: bad Tag" (IM.lookup tg m)
