{-# LANGUAGE PatternGuards, ViewPatterns, Rank2Types, TupleSections, GADTs, DeriveFunctor, DeriveFoldable, ScopedTypeVariables, TypeSynonymInstances #-}
module Termination.Terminate (
        -- * Tag collection combinators
        Embedding, comapEmbedding, alwaysEmbedded, unsafeNeverEmbedded,
        Count, embedCounts, embedTagCounts,
        TagSet, TagMap, TheseTagsMap, refineChainTags, refineByTags,
        
        -- * The termination criterion
        History(..), TermRes(..), emptyHistory, isContinue,
        
        -- * Hack for rollback
        MaybeEvidence(..)
    ) where

import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.IntMap as IM
import qualified Data.IntSet as IS

-- | Predicate that states that there a finite number of values distinguishable by (==) for the given type
class Eq a => Finite a where

instance Finite Tag
instance Finite a => Finite (IM.IntMap a)
instance Finite IS.IntSet


newtype IntMapWithDomain dom a = IMWD { unIMWD :: IM.IntMap a }
                             deriving (Functor, Foldable.Foldable)

instance Zippable (IntMapWithDomain dom) where
    -- The domain equality witnessed by d proves that we are not throwing away any information
    zipWith_ f (IMWD as) (IMWD bs) = IMWD (IM.intersectionWith f as bs)


{-
freshDomain :: IM.IntMap a -> (forall dom. IntMapWithDomain dom a -> res) -> res
freshDomain im k = k (IMWD im)

testDomainEquality :: IntMapWithDomain dom a -> IM.IntMap b -> Maybe (IntMapWithDomain dom b)
testDomainEquality (IMWD im1) im2 = guard (IM.keysSet im1 == IM.keysSet im2) >> return (IMWD im2)


proveDomainEquality :: IM.IntMap a -> IM.IntMap b -> (forall dom. IntMapWithDomain dom a -> IntMapWithDomain dom b -> res) -> res -> res
proveDomainEquality im1 im2 k_eq k_neq = freshDomain im1 (\im1 -> case testDomainEquality im1 im2 of Nothing  -> k_neq
                                                                                                     Just im2 -> k_eq im1 im2)
-}

-- | Type of correct-by-construction embedding operators
--
-- Invariant: for all chains a_1, a_2, ...
-- There exists i, j such that both:
--   1. i < j
--   2. t_i <| t_j
--
-- NB: this is weaker than a WQO because we do not insist on transitivity. I don't think we need it.
-- Nonetheless, all of the definitions below are actually transitive.
-- However, every embedding is necessarily reflexive (consider the infinite chain of equal elements).
--
-- By a Ramsey argument (http://en.wikipedia.org/wiki/Well-quasi-ordering#Properties_of_wqos) this implies
-- that for any chain, there exists a suffix of the chain where every element in the chain participates
-- in at least one infinite ascending sequence of chain elements related pairwise by <|.
data Embedding a why = forall repr. Embedding {
    prepareElement :: a -> repr,
    embedElements :: repr -> repr -> Maybe why
  }

-- | Tests whether two elements are embedding according to the given embedding operator.
--
-- Not very useful in practice (especially because it throws away the "why" information), but useful
-- when defining the semantics of an 'Embedding'.
(<|) :: Embedding a why -> a -> a -> Bool
(<|) (Embedding prepare embed) x y = isJust (prepare x `embed` prepare y)

-- | Build an embedding for a product from embeddings for the components. This is much stronger than
-- 'embedPair' but also unsafe unless some side conditions hold.
--
-- Thus 'unsafeEmbedPair ea eb' is safe exactly when:
--   For all chains (a_1, b_1), (a_2, b_2), ...
--   There exists i, j such that all of the following hold:
--     1. i < j
--     2. a_i <|_ea a_j
--     2. b_i <|_eb b_j
--
-- A sufficient condition for the safety of 'unsafeEmbedPair ea eb' is:
--

--  NOT SUFFICIENT: For all chains (a_1, b_1), (a_2, b_2), ..., each distinct a_i is only paired with finitely many
--                  distinct b_j (though there may be infinitely many distinct b_j overall)
--  WHY: might be infinitely many distinct a_i so no guarantee that the chain (a_i, b_j), (a_i, b_k), (a_i, b_l), ...
--       will ever be infinite, so can't rely on the properties of eb
{-# INLINE unsafeEmbedPair#-}
unsafeEmbedPair :: Embedding a whya -> Embedding b whyb -> Embedding (a, b) (whya, whyb)
unsafeEmbedPair (Embedding prepare_a embed_a) (Embedding prepare_b embed_b) = Embedding (prepare_a *** prepare_b) go
  where go (a1, b1) (a2, b2) = liftM2 (,) (a1 `embed_a` a2) (b1 `embed_b` b2)

-- | Construct an 'Embedding' on the basis of a previous one by elementwise operations on the chain.
--
-- Correct because it maps infinite chains to infinite chains
{-# INLINE comapEmbedding #-}
comapEmbedding :: (b -> a) -> (whya -> whyb) -> Embedding a whya -> Embedding b whyb
comapEmbedding f f_why (Embedding prepare embed) = Embedding (prepare . f) $ \x y -> fmap f_why $ embed x y

-- | Trivial embedding that claims that the elements are always embedded.
--
-- Trivially correct
{-# INLINE alwaysEmbedded #-}
alwaysEmbedded :: Embedding a ()
alwaysEmbedded = Embedding (const ()) $ \_ _ -> Just ()

-- | Trivial embedding that claims that the elements are never embedded.
--
-- Trivially incorrect, but useful for debugging the supercompiler!
{-# INLINE unsafeNeverEmbedded #-}
unsafeNeverEmbedded :: Embedding a ()
unsafeNeverEmbedded = Embedding (const ()) $ \_ _ -> Nothing

-- | Non-negative count of some quantity
type Count = Int

-- | Embedding relationship on chains of 'Count's within a container.
--
-- Correct by pigeonhole principle (relies on the fact that counts are natural numbers)
{-# INLINE embedCounts #-}
embedCounts :: (Zippable t, Foldable.Foldable t) => Embedding (t Count) (t Bool)
embedCounts = Embedding id $ \is1 is2 -> guard (Foldable.sum is1 <= Foldable.sum is2) >> return (fmap (> 0) (zipWith_ (-) is2 is1))

type TagMap = IM.IntMap
type TagSet = IM.IntMap ()
type TheseTagsMap tags = IntMapWithDomain tags

-- | Embedding relationship on 'Count's associated with 'Tag's.
--
-- Correct by construction
{-# INLINE embedTagCounts #-}
embedTagCounts :: Embedding (IntMapWithDomain tags Count) TagSet
embedTagCounts = comapEmbedding id (IM.map (const ()) . IM.filter id . unIMWD) embedCounts
  
-- | Build an embedding for a coproduct from embeddings for the components.
--
-- NB: not currently used.
--
-- Correct because it refines the input chain into two sparser chains
embedEither :: Embedding a why1 -> Embedding b why2 -> Embedding (Either a b) (Either why1 why2)
embedEither (Embedding prepare_a embed_a) (Embedding prepare_b embed_b) = Embedding (either (Left . prepare_a) (Right . prepare_b)) go
  where go (Left a1)  (Left a2)  = fmap Left  (a1 `embed_a` a2)
        go (Right b1) (Right b2) = fmap Right (b1 `embed_b` b2)
        go _          _          = Nothing

-- | Build an embedding for a product from embeddings for the components. You almost always don't want to use
-- this because it is always weaker than using any one of the component embeddings by itself.
--
-- NB: not currently used.
--
-- Correct because it refines the input chain into two sparser chains
embedPair :: Embedding a why1 -> Embedding b why2 -> Embedding (a, b) (Either why1 why2)
embedPair (Embedding prepare_a embed_a) (Embedding prepare_b embed_b) = Embedding (prepare_a *** prepare_b) go
  where go (a1, b1) (a2, b2) = fmap Left (a1 `embed_a` a2) `mplus` fmap Right (b1 `embed_b` b2)

-- | The big hammer: constructs an embedding from two elements of a Cartesian product in a safe way.
--
-- Correct because it effectively refines the input chain into a sparser one per tag-set
refine :: (Finite a) => Embedding b why -> Embedding (a, b) why
refine (Embedding prepare embed) = Embedding (second prepare) $ \(a1, b1) (a2, b2) -> guard (a1 == a2) >> b1 `embed` b2

-- | The big hammer: constructs an embedding from two elements of a Cartesian product, with types
-- appropriately restricted so that this is actually safe.
--
-- Correct because it effectively refines the larger input chain into a smaller one per tag-set
{-# INLINE refineChainTags #-}
{-# DEPRECATED refineChainTags "Unsafe :(" #-}
refineChainTags :: (forall tags. Embedding (TheseTagsMap tags a) why1) -> Embedding b why2 -> Embedding (TagMap a, b) (why1, why2)
refineChainTags embedding_vals embedding_rest = unsafeRefineChainTags embedding_vals' embedding_rest
  where
    -- NB: this is safe because although we fake the tag domain information in the IntMapWithDomain, we check that our lie was
    -- actually correct before we compute the embedding.
    embedding_vals' = case embedding_vals of Embedding prepare_vals embed_vals -> Embedding (\im -> (IM.keysSet im, prepare_vals (IMWD im))) (\(im_keys1, im1) (im_keys2, im2) -> guard (im_keys1 == im_keys2) >> embed_vals im1 im2)
          
    unsafeRefineChainTags :: Embedding (TagMap a) why1 -> Embedding b why2 -> Embedding (TagMap a, b) (why1, why2)
    unsafeRefineChainTags (Embedding prepare_vals embed_vals) (Embedding prepare_rest embed_rest) = Embedding (prepare_vals *** prepare_rest) $ \(im1, b1) (im2, b2) -> liftM2 (,) (embed_vals im1 im2) (embed_rest b1 b2)

-- | Specialisation of the big hammer for the situation where we want to refine by the domain of a map.
-- Certifies that after we test for equality all maps that are embedded will actually have the same domain.
--
-- Correct by construction
{-# INLINE refineByTags #-}
refineByTags :: (forall tags. Embedding (TheseTagsMap tags a) why) -> Embedding (TagMap a) why
--refineByTags embed_vals = comapEmbedding (,()) fst $ refineChainTags embed_vals alwaysEmbedded
refineByTags embed_vals = comapEmbedding (\im -> (IM.keysSet im, IMWD im)) id $ refine embed_vals


newtype History test why extra = History { terminate :: test -> TermRes test why extra }

data TermRes test why extra = Stop why extra (MaybeEvidence extra -> History test why extra) | Continue (extra -> History test why extra)

isContinue :: TermRes test why extra -> Bool
isContinue (Continue _) = True
isContinue _ = False

{-# INLINE emptyHistory #-}
emptyHistory :: forall test why extra. Embedding test why -> History test why extra
emptyHistory (Embedding (prepare :: test -> repr) embed) = History $ go []
  where
    go :: [(repr, extra)] -> test -> TermRes test why extra
    go seen (prepare -> here)
      -- | traceRender (length seen, tagBag here) && False = undefined
      | (why, prev_seen, prev_extra):_ <- [(why, prev_seen, prev_extra) | (prev, prev_extra):prev_seen <- tails (reverse seen), Just why <- [prev `embed` here]]
      , let forget :: MaybeEvidence extra -> History test why extra
            forget MaybeEvidence = History $ go (prev_seen `forgetFutureHistory` seen)
      = Stop why prev_extra forget
      | otherwise
      = Continue (\here_extra -> History $ go ((here, here_extra) : seen))

-- FIXME: make less ugly
data MaybeEvidence extra where
    MaybeEvidence :: MaybeEvidence (Maybe a)

forgetFutureHistory :: [(test, Maybe a)] -> [(test, Maybe a)] -> [(test, Maybe a)]
forgetFutureHistory short long = short ++ fmap (second (const Nothing)) (short `dropBy` long)
