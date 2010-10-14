{-# LANGUAGE PatternGuards, ViewPatterns, Rank2Types, TupleSections, GADTs, DeriveFunctor, DeriveFoldable, ScopedTypeVariables, TypeSynonymInstances #-}
module Termination.Terminate3 (
        -- * Tag collection combinators
        WQO, comapWQO, alwaysEmbedded, unsafeNeverEmbedded,
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

-- | Type of correct-by-construction WQO operators
--
-- Invariant: for all chains a_1, a_2, ...
-- There exists i, j such that both:
--   1. i < j
--   2. t_i <| t_j
--
-- This means that every embedding is necessarily reflexive (consider the infinite chain of equal elements).
-- Furthermore, we insist that <| is transitive.
--
-- By a Ramsey argument (http://en.wikipedia.org/wiki/Well-quasi-ordering#Properties_of_wqos) we have
-- that for any chain, there exists a suffix of the chain where every element in the chain participates
-- in at least one infinite ascending sequence of chain elements related pairwise by <|.
data WQO a why = forall repr. WQO {
    prepareElement :: a -> repr,
    embedElements :: repr -> repr -> Maybe why
  }

-- | Tests whether two elements are embedding according to the given embedding operator.
--
-- Not very useful in practice (especially because it throws away the "why" information), but useful
-- when defining the semantics of an 'WQO'.
(<|) :: WQO a why -> a -> a -> Bool
(<|) (WQO prepare embed) x y = isJust (prepare x `embed` prepare y)

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
unsafeEmbedPair :: WQO a whya -> WQO b whyb -> WQO (a, b) (whya, whyb)
unsafeEmbedPair (WQO prepare_a embed_a) (WQO prepare_b embed_b) = WQO (prepare_a *** prepare_b) go
  where go (a1, b1) (a2, b2) = liftM2 (,) (a1 `embed_a` a2) (b1 `embed_b` b2)

-- | Construct an 'WQO' on the basis of a previous one by elementwise operations on the chain.
--
-- Correct because it maps infinite chains to infinite chains
{-# INLINE comapWQO #-}
comapWQO :: (b -> a) -> (whya -> whyb) -> WQO a whya -> WQO b whyb
comapWQO f f_why (WQO prepare embed) = WQO (prepare . f) $ \x y -> fmap f_why $ embed x y

-- | Trivial embedding that claims that the elements are always embedded.
--
-- Trivially correct
{-# INLINE alwaysEmbedded #-}
alwaysEmbedded :: WQO a ()
alwaysEmbedded = WQO (const ()) $ \_ _ -> Just ()

-- | Trivial embedding that claims that the elements are never embedded.
--
-- Trivially incorrect, but useful for debugging the supercompiler!
{-# INLINE unsafeNeverEmbedded #-}
unsafeNeverEmbedded :: WQO a ()
unsafeNeverEmbedded = WQO (const ()) $ \_ _ -> Nothing

-- | Embedding that insists on exact equality.
--
-- Correctness ensured by the type class context that ensures that there only a finite
-- number of distinct elements that can actually appear in the chain.
{-# INLINE embedEqual #-}
embedEqual :: Finite a => WQO a ()
embedEqual = WQO id (\x y -> guard (x == y) >> return ())

-- | Non-negative count of some quantity
type Count = Int

-- | WQO relationship on chains of 'Count's within a container.
--
-- Correct by pigeonhole principle (relies on the fact that counts are natural numbers)
{-# INLINE embedCounts #-}
embedCounts :: (Zippable t, Foldable.Foldable t) => WQO (t Count) (t Bool)
embedCounts = WQO id $ \is1 is2 -> guard (Foldable.sum is1 <= Foldable.sum is2) >> return (fmap (> 0) (zipWith_ (-) is2 is1))

type TagMap = IM.IntMap
type TagSet = IM.IntMap ()
type TheseTagsMap tags = IntMapWithDomain tags

-- | WQO relationship on 'Count's associated with 'Tag's.
--
-- Correct by construction
{-# INLINE embedTagCounts #-}
embedTagCounts :: WQO (IntMapWithDomain tags Count) TagSet
embedTagCounts = comapWQO id (IM.map (const ()) . IM.filter id . unIMWD) embedCounts
  
-- | Build an embedding for a coproduct from embeddings for the components.
--
-- NB: not currently used.
--
-- Correct because it refines the input chain into two sparser chains
embedEither :: WQO a why1 -> WQO b why2 -> WQO (Either a b) (Either why1 why2)
embedEither (WQO prepare_a embed_a) (WQO prepare_b embed_b) = WQO (either (Left . prepare_a) (Right . prepare_b)) go
  where go (Left a1)  (Left a2)  = fmap Left  (a1 `embed_a` a2)
        go (Right b1) (Right b2) = fmap Right (b1 `embed_b` b2)
        go _          _          = Nothing

-- | Build an embedding for a product from embeddings for the components. You almost always don't want to use
-- this because it is always weaker than using any one of the component embeddings by itself.
--
-- NB: not currently used.
--
-- Correct because it refines the input chain into two sparser chains
embedPair :: WQO a why1 -> WQO b why2 -> WQO (a, b) (Either why1 why2)
embedPair (WQO prepare_a embed_a) (WQO prepare_b embed_b) = WQO (prepare_a *** prepare_b) go
  where go (a1, b1) (a2, b2) = fmap Left (a1 `embed_a` a2) `mplus` fmap Right (b1 `embed_b` b2)

-- | The big hammer: constructs an embedding from two elements of a Cartesian product in a safe way.
--
-- Correct because it effectively refines the input chain into a sparser one per tag-set
refine :: (Finite a) => WQO b why -> WQO (a, b) why
refine (WQO prepare embed) = WQO (second prepare) $ \(a1, b1) (a2, b2) -> guard (a1 == a2) >> b1 `embed` b2

-- | The big hammer: constructs an embedding from two elements of a Cartesian product, with types
-- appropriately restricted so that this is actually safe.
--
-- Correct because it effectively refines the larger input chain into a smaller one per tag-set
{-# INLINE refineChainTags #-}
{-# DEPRECATED refineChainTags "Unsafe :(" #-}
refineChainTags :: (forall tags. WQO (TheseTagsMap tags a) why1) -> WQO b why2 -> WQO (TagMap a, b) (why1, why2)
refineChainTags embedding_vals embedding_rest = unsafeRefineChainTags embedding_vals' embedding_rest
  where
    -- NB: this is safe because although we fake the tag domain information in the IntMapWithDomain, we check that our lie was
    -- actually correct before we compute the embedding.
    embedding_vals' = case embedding_vals of WQO prepare_vals embed_vals -> WQO (\im -> (IM.keysSet im, prepare_vals (IMWD im))) (\(im_keys1, im1) (im_keys2, im2) -> guard (im_keys1 == im_keys2) >> embed_vals im1 im2)
          
    unsafeRefineChainTags :: WQO (TagMap a) why1 -> WQO b why2 -> WQO (TagMap a, b) (why1, why2)
    unsafeRefineChainTags (WQO prepare_vals embed_vals) (WQO prepare_rest embed_rest) = WQO (prepare_vals *** prepare_rest) $ \(im1, b1) (im2, b2) -> liftM2 (,) (embed_vals im1 im2) (embed_rest b1 b2)

-- | Specialisation of the big hammer for the situation where we want to refine by the domain of a map.
-- Certifies that after we test for equality all maps that are embedded will actually have the same domain.
--
-- Correct by construction
{-# INLINE refineByTags #-}
refineByTags :: (forall tags. WQO (TheseTagsMap tags a) why) -> WQO (TagMap a) why
--refineByTags embed_vals = comapWQO (,()) fst $ refineChainTags embed_vals alwaysEmbedded
refineByTags embed_vals = comapWQO (\im -> (IM.keysSet im, IMWD im)) id $ refine embed_vals


data TermRes state why = Stop why | Continue state

isContinue :: TermRes state why -> Bool
isContinue (Continue _) = True
isContinue _ = False

fmap1 :: (state -> state') -> TermRes state why -> TermRes state' why
fmap1 f (Stop a) = Stop a
fmap1 f (Continue a) = Continue (f a)

fmap2 :: (why -> why') -> TermRes state why -> TermRes state why'
fmap2 f (Stop a) = Stop (f a)
fmap2 f (Continue a) = Continue a


data Antistream test why = forall state. Antistream { initialise :: state, consume :: state -> test -> TermRes state why }

liftEmbedWho :: WQO a why -> WQO a (a, why)
liftEmbedWho (WQO prepare embed) = WQO (\a -> (a, prepare a)) (\(a, aprep) (_b, bprep) -> fmap (a,) (embed aprep bprep))

attachExtras :: WQO a why -> WQO (a, extra) (why, extra)
attachExtras wqo = comapWQO id (\((_a, extra), why) -> (why, extra)) $ liftEmbedWho $ comapWQO fst id wqo

{-# INLINE wqoToAntistream #-}
wqoToAntistream :: forall test why. WQO test why -> Antistream test why
wqoToAntistream (WQO (prepare :: test -> repr) embed) = Antistream [] go
  where
    go :: [repr] -> test -> TermRes [repr] why
    go seen (prepare -> here)
      -- | traceRender (length seen, tagBag here) && False = undefined
      | why:_ <- [why | prev <- reverse seen, Just why <- [prev `embed` here]]
      = Stop why
      | otherwise
      = Continue (here : seen)

-- TODO: can have a more efficient version of this using maps when the first WQO is an embedEqual
{-# INLINE embedPairAS #-}
embedPairAS :: forall a b whya whyb. WQO a whya -> Antistream b whyb -> Antistream (a, b) (whya, whyb)
embedPairAS (WQO (prepare :: a -> arepr) embed) (Antistream (initialise :: state) consume)
  = Antistream [] go
  where
    go :: [([arepr], state)] -> (a, b) -> TermRes [([arepr], state)] (whya, whyb)
    go seen (prepare -> arepr, b) = consider_seen [] seen
      where
        consider_seen saw [] = Continue (([arepr], initialise) : saw)
        consider_seen saw ((seen_areprs@(most_recent_arepr:_), seen_state):seen)
          | Just whya <- most_recent_arepr `embed` arepr
          = case consume seen_state b of
              Stop whyb         -> Stop (whya, whyb)
              Continue mk_state -> consider_seen ((arepr : seen_areprs, mk_state) : saw) seen
          | otherwise
          = consider_seen ((seen_areprs, seen_state) : saw) seen

{-# INLINE comapAntistream #-}
comapAntistream :: (b -> a) -> (whya -> whyb) -> Antistream a whya -> Antistream b whyb
comapAntistream f f_why (Antistream initialise consume) = Antistream initialise (\state b -> fmap2 f_why (consume state (f b)))

{-# INLINE embedEitherAS #-}
embedEitherAS :: Antistream a why1 -> Antistream b why2 -> Antistream (Either a b) (Either why1 why2)
embedEitherAS (Antistream initialise_a consume_a) (Antistream initialise_b consume_b) = Antistream (initialise_a, initialise_b) go
 where go (state_a, state_b) (Left a)  = fmap1 (,state_b) $ fmap2 Left  $ consume_a state_a a
       go (state_a, state_b) (Right b) = fmap1 (state_a,) $ fmap2 Right $ consume_b state_b b

{-# INLINE embedPairASWeak #-}
embedPairASWeak :: Antistream a why1 -> Antistream b why2 -> Antistream (a, b) (why1, why2)
embedPairASWeak (Antistream initialise_a consume_a) (Antistream initialise_b consume_b) = Antistream (Continue initialise_a, Continue initialise_b) go
  where go (tr_a, tr_b) (a, b) = case (step tr_a consume_a a, step tr_b consume_b b) of
                                   (Stop why_a, Stop why_b) -> Stop (why_a, why_b)
                                   one_continue             -> Continue one_continue
        
        step (Stop why)       _       _ = Stop why
        step (Continue state) consume a = consume state a


-- | A skolemised version of Antistream
newtype History test why = History { terminate :: test -> TermRes (History test why) why }

antistreamToHistory :: Antistream test why -> History test why
antistreamToHistory (Antistream initialise consume) = History (fmap1 (\state -> antistreamToHistory (Antistream state consume)) . consume initialise)


type Timestamp = [Int]

-- | The initial time. Occurs before every other time.
--  1) For all t. tsBigBang `tsBefore` t
tsBigBang :: Timestamp
tsBigBang = []

-- | Tests the chronological order of timestamps. If 'a `tsBefore` b' then:
--   1) There exists a history (uninterrupted by rollback) that passed from "a" to "b" (possibly in 0 steps)
--   2) We say that "a" is in the effective history of "b"
--   3) This relation is transitive, antisymmetric and reflexive
tsBefore :: Timestamp -> Timestamp -> Bool
tsBefore = isSuffixOf

-- | Returns the unique timestamp that is just before the supplied timestamp. If `predeccesor a == b` then:
--   1) b `tsBefore` a
--   2) b /= a
--   3) There does not exist c. c `tsBefore` a and b `tsBefore` c
--
-- FIXME: what about the big bang? This function is partial!
--predecessor ::

-- | Returns a timestamp with the segment of the effective history between the two
-- supplied timestamps removed from the new effective history. If 'from `rollbackTo` to == rb' then:
--   1) not (rb `tsBefore` from) and not (from `tsBefore` rb) -- i.e. the "from" and "rb" live in different "branches" of history
--   2) not (rb `tsBefore` to)   and not (to `tsBefore` rb)   -- i.e. the "to" and "rb" live in different "branches" of history
--   3) predecessor rb `tsBefore` from and predecessor rb `tsBefore` to
--   4) There does not exist rb'. with this property such that rb `tsBefore` rb'
rollbackTo :: Timestamp -> Timestamp -> Timestamp
rollbackTo from to = go (reverse from) (reverse to) 0 []
  where
    -- Strip the common prefix of both timestamps
    go (x:xs) (y:ys) n res | x == y = go xs ys x (n : res)
    go _      _      n res = n + 1 : res -- The original timestamps were exactly equal, or one was longer


data Timestamped a = TimestampIt { storedAt :: Timestamp, storedWhat :: a }

accessTimestamped :: Timestamped a -> Timestamp -> Maybe a
accessTimestamped tsed ts = guard (storedAt tsed `tsBefore` ts) >> return (storedWhat tsed)


newtype RBAS a whyf = RBAS { unRBAS :: Antistream a (whyf (RBAS a whyf)) }

-- timestampAS :: Antistream (a, Timestamp) (why, Timestamp) -> Antistream a (Bool, why)
-- timestampAS (Antistream initialise consume) = Antistream (initialise, tsBigBang) go
--   where
--     go (state, ts) a = case consume state (a, ts) of
--                           Stop (why, why_ts) -> Stop (why_ts `tsBefore` ts, why) -- rollback state: (state, 0 : ts `rollbackTo` why_ts)
--                           Continue state'    -> Continue (state', 0 : ts)

timestampAS :: Antistream (a, Timestamp) (why, Timestamp) -> RBAS a ((,,) Bool why)
timestampAS (Antistream initialise consume) = RBAS $ Antistream (initialise, tsBigBang) go
  where
    go (state, ts) a = case consume state (a, ts) of
                          Stop (why, why_ts) -> Stop (why_ts `tsBefore` ts, why, RBAS $ Antistream (state, 0 : ts `rollbackTo` why_ts) go)
                          Continue state'    -> Continue (state', 0 : ts)


-- FIXME: make less ugly
data MaybeEvidence extra where
    MaybeEvidence :: MaybeEvidence (Maybe a)

forgetFutureHistory :: [(test, Maybe a)] -> [(test, Maybe a)] -> [(test, Maybe a)]
forgetFutureHistory short long = short ++ fmap (second (const Nothing)) (short `dropBy` long)
