{-# LANGUAGE BangPatterns, TupleSections, Rank2Types #-}
module Size.Deeds (
    Unclaimed, Deeds,
    mkDeeds,
    claimDeed, claimDeeds,
    releaseDeedDeep, releaseDeedDescend_,
    
    -- * Deed allocation policy
    apportion,
    mkEmptyDeeds, releaseDeedsTo,
    
    -- * Sanity checking
    noChange, noGain
  ) where

import StaticFlags
import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import Data.Tree
import Data.Ord (comparing)


-- | Number of unclaimed deeds. Invariant: always greater than or equal to 0
type Unclaimed = Int
data Deeds = Local LocalDeeds | Global GlobalDeeds

-- | A deed supply local to each subterm of the input.
--
-- TODO: could be slightly neater: only need to store Deeds for the *leaves* of the tree, and a mapping that
-- tells us which leaves the node corresponding to any given Tag dominates.
data LocalDeeds = LocalDeeds {
    rebuild :: Tree Unclaimed -> Doc,
    localChildren :: TagTree ((,) Unclaimed)
  }

-- | A deed supply shared amongst all expressions.
data GlobalDeeds = GlobalDeeds {
    globalUnclaimed :: Unclaimed,
    globalChildren :: TagTree Identity
  }

-- TODO: this module is rather ugly, but this data type is a particular eyesore
data TagTree f = TagTree {
    rootTag :: Tag,
    childrenMap :: IM.IntMap (f [Tag])
  }

instance NFData Deeds where
    rnf (Local a) = rnf a
    rnf (Global a) = rnf a

instance NFData LocalDeeds where
    rnf (LocalDeeds a b) = a `seq` rnf b

instance NFData GlobalDeeds where    
    rnf (GlobalDeeds a b)  = rnf a `seq` rnf b

instance NFData1 f => NFData (TagTree f) where
    rnf (TagTree a b) = rnf a `seq` rnf b

instance Pretty Deeds where
    pPrint (Local ldeeds)  = pPrint ldeeds
    pPrint (Global gdeeds) = pPrint gdeeds

instance Pretty LocalDeeds where
    pPrint ldeeds = rebuild ldeeds (reifyDeedsTree (localChildren ldeeds))
      where
        -- NB: the correctness of this function depends on the Tags in the input all being distinct
        reifyDeedsTree :: TagTree ((,) Unclaimed) -> Tree Unclaimed
        reifyDeedsTree ttree = go (rootTag ttree)
          where
            go :: Tag -> Tree Unclaimed
            go tg = Node unclaimed (map go child_tgs)
              where !(unclaimed, child_tgs) = lookupTag tg ttree

instance Pretty GlobalDeeds where
    pPrint gdeeds = text "Unclaimed:" <+> pPrint (globalUnclaimed gdeeds)


mkDeeds :: Unclaimed -> (Tree Tag, Tree Tag -> Doc) -> Deeds
mkDeeds k (t@(Node root_tg _), rb)
  | gLOBAL_DEEDS = Global $ GlobalDeeds (k * length (flatten t)) (TagTree root_tg (fmap I children))
  | otherwise    = -- traceRender ("mkDeeds", fmap (const (1 :: Int)) t, fmap (const (1 :: Int)) (reifyDeedsTree deeds), rb (fmap (const (1 :: Int)) (reifyDeedsTree deeds))) $
                   Local $ LocalDeeds rb (TagTree root_tg (fmap (k,) children))
  where
    children = go IM.empty t
    go m (Node tg trees) = foldl' go (IM.insert tg (map rootLabel trees) m) trees

claimDeed :: Deeds -> TagSet -> Maybe Deeds
claimDeed deeds tg = claimDeeds deeds tg 1

claimDeeds :: Deeds -> TagSet -> Int -> Maybe Deeds
claimDeeds deeds tgs i = IS.fold (\tg mb_deeds -> mb_deeds >>= \deeds -> claimDeeds1 deeds tg i) (return deeds) tgs

-- NB: it is OK if the number of deeds to claim is negative -- that just causes some deeds to be released
claimDeeds1 :: Deeds -> Tag -> Int -> Maybe Deeds
claimDeeds1 deeds _ _ | not dEEDS = Just deeds
claimDeeds1 (Local ldeeds) tg want = guard (unclaimed >= want) >> foldM (\deeds tg -> claimDeeds1 deeds tg want) (Local (ldeeds { localChildren = updateTag tg (unclaimed - want, child_tgs) (localChildren ldeeds) })) child_tgs
  where !(unclaimed, child_tgs) = lookupTag tg (localChildren ldeeds)
claimDeeds1 (Global gdeeds) tg want = guard (globalUnclaimed gdeeds >= want) >> foldM (\deeds tg -> claimDeeds1 deeds tg want) (Global (gdeeds { globalUnclaimed = globalUnclaimed gdeeds - want })) child_tgs
  where !(I child_tgs) = lookupTag tg (globalChildren gdeeds)

releaseDeedDeep :: Deeds -> TagSet -> Deeds
releaseDeedDeep deeds tgs = IS.fold (flip releaseDeedDeep1) deeds tgs

releaseDeedDeep1 :: Deeds -> Tag -> Deeds
releaseDeedDeep1 deeds tg = foldl' releaseDeedDeep1 deeds' child_tgs
  where (deeds', child_tgs) = releaseDeedDescend1 deeds tg

releaseDeedDescend1 :: Deeds -> Tag -> (Deeds, [Tag])
releaseDeedDescend1 (Local ldeeds) tg = (Local (ldeeds { localChildren = updateTag tg (unclaimed + 1, child_tgs) (localChildren ldeeds) }), child_tgs)
  where !(unclaimed, child_tgs) = lookupTag tg (localChildren ldeeds)
releaseDeedDescend1 (Global gdeeds) tg = (Global (gdeeds { globalUnclaimed = globalUnclaimed gdeeds + 1 }), child_tgs)
  where !(I child_tgs) = lookupTag tg (globalChildren gdeeds)

releaseDeedDescend_ :: Deeds -> TagSet -> Deeds
releaseDeedDescend_ deeds tgs = IS.fold (flip releaseDeedDescend1_) deeds tgs

releaseDeedDescend1_ :: Deeds -> Tag -> Deeds
releaseDeedDescend1_ deeds tg = fst (releaseDeedDescend1 deeds tg)


lookupTag :: Tag -> TagTree f -> f [Tag]
lookupTag tg ttree = expectJust "lookupTag: bad Tag" (IM.lookup tg (childrenMap ttree))

updateTag :: Tag -> f [Tag] -> TagTree f -> TagTree f
updateTag tg x ttree = ttree { childrenMap = IM.insert tg x (childrenMap ttree) }

ffmapTags :: (forall a. f a -> g a) -> TagTree f -> TagTree g
ffmapTags phi ttree = TagTree { rootTag = rootTag ttree, childrenMap = IM.map phi (childrenMap ttree) }

unionTagsWith :: (f [Tag] -> f [Tag] -> f [Tag]) -> TagTree f -> TagTree f -> TagTree f
unionTagsWith comb left right = TagTree { rootTag = rootTag right, childrenMap = IM.unionWith comb (childrenMap left) (childrenMap right) }


apportion :: Deeds -> [Int] -> [Deeds]
apportion _               []        = error "apportion: empty list"
apportion (Local ldeeds)  weighting = [Local (ldeeds { localChildren = ffmapTags (\(unclaimed, tags) -> (sel (apportionN unclaimed weighting), tags)) (localChildren ldeeds) }) | (sel, _) <- listSelectors `zip` weighting]
apportion (Global gdeeds) weighting = [Global (gdeeds { globalUnclaimed = unclaimed }) | unclaimed <- apportionN (globalUnclaimed gdeeds) weighting]

-- | Splits up a number evenly across several partitions in proportions to weights given to those partitions.
--
-- > sum (apportionN n weights) == n
apportionN :: Int -> [Int] -> [Int]
apportionN _      []        = error "apportionN: empty list"
apportionN orig_n weighting = result
  where
    fracs :: [Rational]
    fracs = assertRender (text "apportionN: must have at least one non-zero weight") (denominator /= 0) $
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
noChange = andZipDeeds (==)
noGain = andZipDeeds (>=)

andZipDeeds :: (Unclaimed -> Unclaimed -> Bool)
            -> Deeds -> Deeds -> Bool
andZipDeeds f (Local ldeeds1) (Local ldeeds2) = IM.keysSet children1 == IM.keysSet children2 && Foldable.and (IM.intersectionWith (\(unclaimed1, _) (unclaimed2, _) -> unclaimed1 `f` unclaimed2) children1 children2)
  where (children1, children2) = (childrenMap (localChildren ldeeds1), childrenMap (localChildren ldeeds2))
andZipDeeds f (Global gdeeds1) (Global gdeeds2) = globalUnclaimed gdeeds1 `f` globalUnclaimed gdeeds2
andZipDeeds _ _ _ = error "andZipDeeds: unsupported loss combination"


-- | Puts any unclaimed deeds in the first argument into the unclaimed deed store of the second argument
releaseDeedsTo :: Deeds -> Deeds -> Deeds
releaseDeedsTo (Local  ldeeds_release) (Local  ldeeds_to) = Local  (ldeeds_to { localChildren = unionTagsWith (\(unclaimed_l, tgs_l) (unclaimed_r, _tgs_r) -> (unclaimed_l + unclaimed_r, tgs_l)) (localChildren ldeeds_release) (localChildren ldeeds_to) } )
releaseDeedsTo (Global gdeeds_release) (Global gdeeds_to) = Global (gdeeds_to { globalUnclaimed = globalUnclaimed gdeeds_to + globalUnclaimed gdeeds_release })
releaseDeedsTo _ _ = error "releaseDeedsTo: unsupported release combination"

-- | Returned 'Deeds' are the identity element of 'releaseDeedsTo'
--
-- mkEmptyDeeds deeds `releaseDeedsTo` deeds == deeds
-- deeds `releaseDeedsTo` mkEmptyDeeds deeds == deeds
mkEmptyDeeds :: Deeds -> Deeds
mkEmptyDeeds (Local ldeeds)  = Local (ldeeds { localChildren = ffmapTags (\(_, tgs) -> (0, tgs)) (localChildren ldeeds) })
mkEmptyDeeds (Global gdeeds) = Global (gdeeds { globalUnclaimed = 0 })
