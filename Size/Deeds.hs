{-# LANGUAGE BangPatterns, TupleSections #-}
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
data Deeds = Local LocalDeeds | Global GlobalDeeds

-- | A deed supply local to each subterm of the input.
--
-- TODO: could be slightly neater: only need to store Deeds for the *leaves* of the tree, and a mapping that
-- tells us which leaves the node corresponding to any given Tag dominates.
data LocalDeeds = LocalDeeds {
    localRootTag :: Tag,
    rebuild :: Tree Unclaimed -> Doc,
    unclaimedMap :: IM.IntMap ([Tag], Unclaimed)
  }

-- | A deed supply shared amongst all expressions.
data GlobalDeeds = GlobalDeeds {
    globalUnclaimed :: Unclaimed,
    globalRootTag :: Tag,
    childrenMap :: IM.IntMap [Tag]
  }

instance NFData Deeds where
    rnf (Local a) = rnf a
    rnf (Global a) = rnf a

instance NFData LocalDeeds where
    rnf (LocalDeeds a b c) = rnf a `seq` b `seq` rnf c

instance NFData GlobalDeeds where    
    rnf (GlobalDeeds a b c)  = rnf a `seq` rnf b `seq` rnf c

instance Pretty Deeds where
    pPrint (Local ldeeds)  = pPrint ldeeds
    pPrint (Global gdeeds) = pPrint gdeeds

instance Pretty LocalDeeds where
    pPrint ldeeds = rebuild ldeeds (reifyDeedsTree ldeeds)
      where
        -- NB: the correctness of this function depends on the Tags in the input all being distinct
        reifyDeedsTree :: LocalDeeds -> Tree Unclaimed
        reifyDeedsTree deeds = go (localRootTag deeds)
          where
            go :: Tag -> Tree Unclaimed
            go tg = Node unclaimed (map go child_tgs)
              where !(child_tgs, unclaimed) = lookupTag tg (unclaimedMap deeds)

instance Pretty GlobalDeeds where
    pPrint gdeeds = text "Unclaimed:" <+> pPrint (globalUnclaimed gdeeds)


mkDeeds :: Unclaimed -> (Tree Tag, Tree Tag -> Doc) -> Deeds
mkDeeds k (t@(Node root_tg _), rb)
  | gLOBAL_DEEDS = Global gdeeds
  | otherwise    = -- traceRender ("mkDeeds", fmap (const (1 :: Int)) t, fmap (const (1 :: Int)) (reifyDeedsTree deeds), rb (fmap (const (1 :: Int)) (reifyDeedsTree deeds))) $
                   Local ldeeds
  where
    gdeeds = GlobalDeeds (k * length (flatten t)) root_tg children
    ldeeds = LocalDeeds root_tg rb (fmap (,k) children)
    
    children = go IM.empty t
    go m (Node tg trees) = foldl' go (IM.insert tg (map rootLabel trees) m) trees

claimDeed :: Deeds -> Tag -> Maybe Deeds
claimDeed deeds tg = claimDeeds deeds tg 1

-- NB: it is OK if the number of deeds to claim is negative -- that just causes some deeds to be released
claimDeeds :: Deeds -> Tag -> Int -> Maybe Deeds
claimDeeds deeds _ _ | not dEEDS = Just deeds
claimDeeds (Local ldeeds) tg want = guard (unclaimed >= want) >> foldM claimDeed (Local (ldeeds { unclaimedMap = IM.insert tg (child_tgs, unclaimed - want) (unclaimedMap ldeeds) })) child_tgs
  where !(child_tgs, unclaimed) = lookupTag tg (unclaimedMap ldeeds)
claimDeeds (Global gdeeds) tg want = guard (globalUnclaimed gdeeds >= want) >> foldM claimDeed (Global (gdeeds { globalUnclaimed = globalUnclaimed gdeeds - want })) child_tgs
  where child_tgs = lookupTag tg (childrenMap gdeeds)

releaseDeedDeep :: Deeds -> Tag -> Deeds
releaseDeedDeep deeds tg = foldl' releaseDeedDeep deeds' child_tgs
  where (deeds', child_tgs) = releaseDeedDescend deeds tg

releaseDeedDescend :: Deeds -> Tag -> (Deeds, [Tag])
releaseDeedDescend (Local ldeeds) tg = (Local (ldeeds { unclaimedMap = IM.insert tg (child_tgs, unclaimed + 1) (unclaimedMap ldeeds) }), child_tgs)
  where !(child_tgs, unclaimed) = lookupTag tg (unclaimedMap ldeeds)
releaseDeedDescend (Global gdeeds) tg = (Global (gdeeds { globalUnclaimed = globalUnclaimed gdeeds + 1 }), lookupTag tg (childrenMap gdeeds))

releaseDeedDescend_ :: Deeds -> Tag -> Deeds
releaseDeedDescend_ deeds tg = fst (releaseDeedDescend deeds tg)

lookupTag :: Tag -> IM.IntMap a -> a
lookupTag tg m = expectJust "lookupTag: bad Tag" (IM.lookup tg m)
