{-# LANGUAGE PatternGuards, ViewPatterns, Rank2Types, TupleSections, GADTs, DeriveFunctor, DeriveFoldable, ScopedTypeVariables, TypeSynonymInstances, GeneralizedNewtypeDeriving #-}
module Termination.Terminate4 (
        silly
    ) where

import Utilities

import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable
import Data.Monoid

import Data.Either (partitionEithers)

import qualified Data.IntMap as IM
import qualified Data.IntSet as IS
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Tree as T

import Unsafe.Coerce


-- | Predicate that states that there exists a finite number of values distinguishable by (==) for the given type
class Eq a => Finite a where

instance Finite Tag
instance Finite TagSet
instance Finite v => Finite (TagMap v)

instance Finite v => Finite (S.Set v)
instance (Finite k, Finite v) => Finite (M.Map k v)


-- | A class for objects that are both cofunctorial and functorial, in different type parameters.
-- Instances must satisfy the following laws:
--
-- > precomp id == id
-- > precomp f . precomp g == precomp (g . f)
--
-- > postcomp id == id
-- > postcomp f . postcomp g == precomp (f . g)
class Prearrow r where
    precomp  :: (a -> b) -> r b c -> r a c
    postcomp :: (b -> c) -> r a b -> r a c

instance Prearrow (->) where
    precomp  f g = g . f
    postcomp f g = f . g


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

instance Prearrow WQO where
    -- This defines a wqo because it just maps infinite chains to infinite chains.
    {-# INLINE precomp #-}
    precomp f (WQO prepare embed) = WQO (prepare . f) embed

    -- This defines a wqo trivially - it only effects the 'why' information.
    {-# INLINE postcomp #-}
    postcomp f_why (WQO prepare embed) = WQO prepare $ \x y -> fmap f_why $ embed x y

lazy :: forall a why. WQO a why -> WQO a why
lazy wqo = WQO (case wqo of WQO prepare _ -> unsafeCoerce prepare :: a -> ()) (case wqo of WQO _ embed -> unsafeCoerce embed)

-- | Trivial embedding that claims that the elements are always embedded.
--
-- Trivially correct.
{-# INLINE always #-}
always :: WQO a ()
always = WQO (const ()) $ \_ _ -> Just ()

-- | Trivial embedding that claims that the elements are never embedded.
--
-- Trivially incorrect, but useful for debugging the supercompiler!
{-# INLINE unsafeNever #-}
unsafeNever :: WQO a ()
unsafeNever = WQO (const ()) $ \_ _ -> Nothing

-- | Embedding that insists on exact equality.
--
-- Correctness ensured by the type class context that ensures that there only a finite
-- number of distinct elements that can actually appear in the chain.
{-# INLINE equal #-}
equal :: Finite a => WQO a ()
equal = WQO id $ \x y -> guard (x == y) >> return ()

-- | Natural numbers on the cheap (for efficiency reasons)
type Nat = Int

-- | Embedding on natural numbers.
--
-- Correct by pigeonhole principle (relies on the fact that natural numbers have a lower bound).
{-# INLINE nat #-}
nat :: WQO Nat ()
nat = WQO id $ \x y -> guard (x <= y) >> return ()

-- | Build an embedding for a coproduct from embeddings for the components.
--
-- Correct because it refines the input chain into two sparser chains. This is also a special case of the Finite
-- Union Lemma in "Well-Quasi-Ordering, The Tree Theorem, and Vazsonyi's Conjecture" (Kruskal, 1960).
{-# INLINE coprod #-}
coprod :: WQO a whya -> WQO b whyb -> WQO (Either a b) (Either whya whyb)
coprod (WQO prepare_a embed_a) (WQO prepare_b embed_b) = WQO (either (Left . prepare_a) (Right . prepare_b)) go
  where go (Left a1)  (Left a2)  = fmap Left  (a1 `embed_a` a2)
        go (Right b1) (Right b2) = fmap Right (b1 `embed_b` b2)
        go _          _          = Nothing

-- | Build an embedding for a product from embeddings for the components.
--
-- To see why this is defines a wqo, consider a violating chain of (a, b) pairs. Since a is wqo, by a Ramsey argument, we
-- must have an infinite chain of just a elements where each one is pairwise embedded (and hence all embedded into the
-- first element of the chain, by transitivity). Now consider the infinite chain of associated b elements. Since b is wqo
-- this chain must be finite - a contradiction. A special case of the Finite Cartesian Product Lemma in "Well-Quasi-Ordering,
-- The Tree Theorem, and Vazsonyi's Conjecture" (Kruskal, 1960).
{-# INLINE prod #-}
prod :: WQO a whya -> WQO b whyb -> WQO (a, b) (whya, whyb)
prod (WQO prepare_a embed_a) (WQO prepare_b embed_b) = WQO (prepare_a *** prepare_b) go
  where go (a1, b1) (a2, b2) = liftM2 (,) (a1 `embed_a` a2) (b1 `embed_b` b2)

-- | Embedding on sets of things, derived from an embedding on the elements.
--
-- Correctness proved as a lemma in e.g. "On well-quasi-ordering finite trees" (Nash-Williams, 1963)
{-# INLINE set #-}
set :: Ord a => WQO a why -> WQO (S.Set a) (M.Map a why)
set (WQO prepare embed) = WQO (map (prepare &&& id) . S.toList) $ \xs ys -> Foldable.foldrM (\(xrepr, x) whys -> fmap (\why -> M.insert x why whys) $ getFirst (Foldable.foldMap (\(yrepr, _y) -> First (xrepr `embed` yrepr)) ys)) M.empty xs

-- | Embedding on finite sequences of things, derived from an ordering on the elemnts.
--
-- Correctness proved by the Finite Sequence Theorem in "Well-Quasi-Ordering, The Tree Theorem, and Vazsonyi's Conjecture" (Kruskal, 1960).
{-# INLINE list #-}
list :: WQO a why -> WQO [a] [(a, why)]
list (WQO prepare embed) = WQO (map (prepare &&& id)) $ go []
  where
    -- Kruskal sez: "Intuitively, one sequence is less than another if some subsequence of the greater sequence majorizes the smaller sequence term by term"
    -- But he is misleading you. If you parse his actual definitions, xs <| ys iff there is way to map the elements of xs onto some (possibly non-consecutive)
    -- subsequence of ys such that for each resulting pair, we have that x <| y.
    go res ((xrepr, x):xs) ((yrepr, y):ys)
      | Just why <- xrepr `embed` yrepr = go ((y, why) : res) xs ys
      | otherwise                       = go res ((xrepr, x):xs) ys
    go _   (_:_)  []     = Nothing
    go res []     _      = Just (reverse res)

-- | Embedding on things with exactly corresponding "shapes", derived from an embedding on the elements.
--
-- Correct (for finite "shapes") because it can be implemented by mapping the elements of the container to a fixed length
-- tuple and then iterating the 'product' lemma.
{-# INLINE zippable #-}
zippable :: (Zippable t, Traversable.Traversable t) => WQO a why -> WQO (t a) (t why)
zippable (WQO prepare embed) = WQO (fmap prepare) $ \xs ys -> Traversable.sequenceA (zipWith_ embed xs ys)


newtype Vec n a = UnsafeCertifyVecLength { unVec :: [a] }
                deriving (Functor, Foldable.Foldable, Traversable.Traversable)

instance Zippable (Vec n) where
    zipWith_ f (UnsafeCertifyVecLength xs) (UnsafeCertifyVecLength ys) = UnsafeCertifyVecLength (zipWith f xs ys)

-- | Embedding on sequences of trees given an embedding on the vertex labellings.
--
-- Correctness proved by the Tree Therom in "Well-Quasi-Ordering, The Tree Theorem, and Vazsonyi's Conjecture" (Kruskal, 1960),
-- but just a correct-by-construction combinator here, in the style of "On well-quasi-ordering finite trees" (Nash-Williams, 1963).
{-# INLINE tree #-}
tree :: forall a why. WQO a why -> WQO (T.Tree a) (why, [T.Tree (a, why)])
tree wqo = wqo_tree
  where
    wqo_tree :: WQO (T.Tree a) (why, [T.Tree (a, why)])
    wqo_tree = lazy $ precomp (\(T.Node x txs) -> (x, txs)) (postcomp (\(why, twhys) -> (why, [T.Node (a, why) ts | (T.Node a _, (why, ts)) <- twhys])) wqo_treeish)
    
    wqo_treeish :: WQO (a, [T.Tree a]) (why, [(T.Tree a, (why, [T.Tree (a, why)]))])
    wqo_treeish = prod wqo (list wqo_tree)


-- tree_equal :: WQO (T.Tree a) [T.Tree a]
-- tree_equal = postcomp (\((), t) -> map (fmap fst) t) $ tree equal


-- data TermRes state why = Stop why | Continue state
-- 
-- isContinue :: TermRes state why -> Bool
-- isContinue (Continue _) = True
-- isContinue _ = False
-- 
-- fmap1 :: (state -> state') -> TermRes state why -> TermRes state' why
-- fmap1 f (Stop a) = Stop a
-- fmap1 f (Continue a) = Continue (f a)
-- 
-- fmap2 :: (why -> why') -> TermRes state why -> TermRes state why'
-- fmap2 f (Stop a) = Stop (f a)
-- fmap2 f (Continue a) = Continue a
-- 
-- 
-- data Antistream test why = forall state. Antistream { initialise :: state, consume :: state -> test -> TermRes state why }
-- 
-- liftEmbedWho :: WQO a why -> WQO a (a, why)
-- liftEmbedWho (WQO prepare embed) = WQO (\a -> (a, prepare a)) (\(a, aprep) (_b, bprep) -> fmap (a,) (embed aprep bprep))
-- 
-- attachExtras :: WQO a why -> WQO (a, extra) (why, extra)
-- attachExtras wqo = comapWQO id (\((_a, extra), why) -> (why, extra)) $ liftEmbedWho $ comapWQO fst id wqo
-- 
-- -- fmap1 (\a -> (a, ())) (fmap2 (\(why, ()) -> why) (embedPairAS wqo (wqoToAntistream alwaysEmbedded))) == wqoToAntistream wqo
-- {-# INLINE wqoToAntistream #-}
-- wqoToAntistream :: forall test why. WQO test why -> Antistream test why
-- wqoToAntistream (WQO (prepare :: test -> repr) embed) = Antistream [] go
--   where
--     go :: [repr] -> test -> TermRes [repr] why
--     go seen (prepare -> here)
--       -- | traceRender (length seen, tagBag here) && False = undefined
--       | why:_ <- [why | prev <- reverse seen, Just why <- [prev `embed` here]]
--       = Stop why
--       | otherwise
--       = Continue (here : seen)
-- 
-- -- fmap2 (\((), why) -> why) (embedPairAS embedEqual (wqoToAntistream wqo)) == wqoToAntistream (refine wqo)
-- {-# INLINE embedPairAS #-}
-- embedPairAS :: forall a b whya whyb. WQO a whya -> Antistream b whyb -> Antistream (a, b) (whya, whyb)
-- embedPairAS (WQO (prepare :: a -> arepr) embed) (Antistream (initialise :: state) consume)
--   = Antistream [] go
--   where
--     -- There are several ways to write this function:
--     --  1) Store several states for each arepr and Stop when stepping any of them stops
--     --     - but this does not give TagSet behaviour when applied to embedEqual (it is a bit more eager to stop)
--     --     - we can get this variant with an allConsume that throws away Continue instead of Stop
--     --  2) Store one state for each arepr, but choose a Continuing state from those you embed in to when stepping (if one exists)
--     --     - this gives TagSet behaviour exactly
--     --  3) Store several states for each arepr and Stop when all of them do (this feels wrong, but I'm pretty sure it's OK!)
--     --     - this gives TagSet behaviour exactly, but can be stronger than 2) (for some choices of WQOs)
--     go :: [(arepr, state)] -> (a, b) -> TermRes [(arepr, state)] (whya, whyb)
--     go seens (prepare -> arepr, b)
--       -- NB: when adding an element of "b" for the very first time, for compability with TagBag semantics we would like to
--       -- consume that element of "b" here and now
--       | null seens_embedded  = case consume initialise b of Stop whyb            -> Stop (case arepr `embed` arepr of Just whya -> whya; Nothing -> error "Impossible: non-reflexive WQO!", whyb)
--                                                             Continue seen_state' -> Continue ((arepr, seen_state') : seens_others)
--       -- Uncomment (and additionally cons on (arepr, initialise) in the last branch) to get variant 1):
--       -- | whyb:_ <- whybs      = Stop (whya, whyb)
--       | null seens_embedded' = Stop (head whys) -- TODO: could return all reasons? NB: list guaranteed to be non empty!
--       -- Uncomment to get variant 2):
--       -- | otherwise            = Continue (head seens_embedded' : seens_others)
--       | otherwise            = Continue (seens_embedded' ++ seens_others) -- NB: In variant 3), I don't think it's safe to cons (arepr, initialise) on to the state list here
--       where
--         (seens_others, seens_embedded) = partitionEithers [case seen_arepr `embed` arepr of Nothing   -> Left seen
--                                                                                             Just whya -> Right (whya, seen_state)
--                                                           | seen@(seen_arepr, seen_state) <- seens]
--         (whys, seens_embedded') = partitionEithers [case consume seen_state b of Stop whyb            -> Left (whya, whyb)
--                                                                                  Continue seen_state' -> Right (arepr, seen_state')
--                                                    | (whya, seen_state) <- seens_embedded]
-- 
-- {- {-# RULES "embedPairAS/embedEqual" forall stream. embedPairAS embedEqual stream = embedPairASEqual stream #-} -}
-- 
-- {-# INLINE embedPairASEqual #-}
-- embedPairASEqual :: forall a b whyb. (Finite a, Ord a) => Antistream b whyb -> Antistream (a, b) ((), whyb)
-- embedPairASEqual (Antistream (initialise :: state) consume)
--   = Antistream M.empty go
--   where
--     go :: M.Map a state -> (a, b) -> TermRes (M.Map a state) ((), whyb)
--     go seen (a, b) = case consume (M.lookup a seen `orElse` initialise) b of
--         Stop whyb            -> Stop ((), whyb)
--         Continue seen_state' -> Continue (M.insert a seen_state' seen)
-- 
-- {-# INLINE comapAntistream #-}
-- comapAntistream :: (b -> a) -> (whya -> whyb) -> Antistream a whya -> Antistream b whyb
-- comapAntistream f f_why (Antistream initialise consume) = Antistream initialise (\state b -> fmap2 f_why (consume state (f b)))
-- 
-- {-# INLINE embedEitherAS #-}
-- embedEitherAS :: Antistream a why1 -> Antistream b why2 -> Antistream (Either a b) (Either why1 why2)
-- embedEitherAS (Antistream initialise_a consume_a) (Antistream initialise_b consume_b) = Antistream (initialise_a, initialise_b) go
--  where go (state_a, state_b) (Left a)  = fmap1 (,state_b) $ fmap2 Left  $ consume_a state_a a
--        go (state_a, state_b) (Right b) = fmap1 (state_a,) $ fmap2 Right $ consume_b state_b b
-- 
-- {-# INLINE embedPairASWeak #-}
-- embedPairASWeak :: Antistream a why1 -> Antistream b why2 -> Antistream (a, b) (why1, why2)
-- embedPairASWeak (Antistream initialise_a consume_a) (Antistream initialise_b consume_b) = Antistream (Continue initialise_a, Continue initialise_b) go
--   where go (tr_a, tr_b) (a, b) = case (step tr_a consume_a a, step tr_b consume_b b) of
--                                    (Stop why_a, Stop why_b) -> Stop (why_a, why_b)
--                                    one_continue             -> Continue one_continue
--         
--         step (Stop why)       _       _ = Stop why
--         step (Continue state) consume a = consume state a
-- 
-- 
-- -- | A skolemised version of Antistream
-- newtype History test why = History { terminate :: test -> TermRes (History test why) why }
-- 
-- antistreamToHistory :: Antistream test why -> History test why
-- antistreamToHistory (Antistream initialise consume) = History (fmap1 (\state -> antistreamToHistory (Antistream state consume)) . consume initialise)
-- 
-- 
-- type Timestamp = [Int]
-- 
-- -- | The initial time. Occurs before every other time.
-- --  1) For all t. tsBigBang `tsBefore` t
-- tsBigBang :: Timestamp
-- tsBigBang = []
-- 
-- -- | Tests the chronological order of timestamps. If 'a `tsBefore` b' then:
-- --   1) There exists a history (uninterrupted by rollback) that passed from "a" to "b" (possibly in 0 steps)
-- --   2) We say that "a" is in the effective history of "b"
-- --   3) This relation is transitive, antisymmetric and reflexive
-- tsBefore :: Timestamp -> Timestamp -> Bool
-- tsBefore = isSuffixOf
-- 
-- -- | Returns the unique timestamp that is just before the supplied timestamp. If `predeccesor a == b` then:
-- --   1) b `tsBefore` a
-- --   2) b /= a
-- --   3) There does not exist c. c `tsBefore` a and b `tsBefore` c
-- --
-- -- FIXME: what about the big bang? This function is partial!
-- --predecessor ::
-- 
-- -- | Returns a timestamp with the segment of the effective history between the two
-- -- supplied timestamps removed from the new effective history. If 'from `rollbackTo` to == rb' then:
-- --   1) not (rb `tsBefore` from) and not (from `tsBefore` rb) -- i.e. the "from" and "rb" live in different "branches" of history
-- --   2) not (rb `tsBefore` to)   and not (to `tsBefore` rb)   -- i.e. the "to" and "rb" live in different "branches" of history
-- --   3) predecessor rb `tsBefore` from and predecessor rb `tsBefore` to
-- --   4) There does not exist rb'. with this property such that rb `tsBefore` rb'
-- rollbackTo :: Timestamp -> Timestamp -> Timestamp
-- rollbackTo from to = go (reverse from) (reverse to) 0 []
--   where
--     -- Strip the common prefix of both timestamps
--     go (x:xs) (y:ys) n res | x == y = go xs ys x (n : res)
--     go _      _      n res = n + 1 : res -- The original timestamps were exactly equal, or one was longer
-- 
-- 
-- data Timestamped a = TimestampIt { storedAt :: Timestamp, storedWhat :: a }
-- 
-- accessTimestamped :: Timestamped a -> Timestamp -> Maybe a
-- accessTimestamped tsed ts = guard (storedAt tsed `tsBefore` ts) >> return (storedWhat tsed)
-- 
-- 
-- newtype RBAS a whyf = RBAS { unRBAS :: Antistream a (whyf (RBAS a whyf)) }
-- 
-- -- timestampAS :: Antistream (a, Timestamp) (why, Timestamp) -> Antistream a (Bool, why)
-- -- timestampAS (Antistream initialise consume) = Antistream (initialise, tsBigBang) go
-- --   where
-- --     go (state, ts) a = case consume state (a, ts) of
-- --                           Stop (why, why_ts) -> Stop (why_ts `tsBefore` ts, why) -- rollback state: (state, 0 : ts `rollbackTo` why_ts)
-- --                           Continue state'    -> Continue (state', 0 : ts)
-- 
-- timestampAS :: Antistream (a, Timestamp) (why, Timestamp) -> RBAS a ((,,) Bool why)
-- timestampAS (Antistream initialise consume) = RBAS $ Antistream (initialise, tsBigBang) go
--   where
--     go (state, ts) a = case consume state (a, ts) of
--                           Stop (why, why_ts) -> Stop (why_ts `tsBefore` ts, why, RBAS $ Antistream (state, 0 : ts `rollbackTo` why_ts) go)
--                           Continue state'    -> Continue (state', 0 : ts)
-- 
-- 
-- -- FIXME: make less ugly
-- data MaybeEvidence extra where
--     MaybeEvidence :: MaybeEvidence (Maybe a)
-- 
-- forgetFutureHistory :: [(test, Maybe a)] -> [(test, Maybe a)] -> [(test, Maybe a)]
-- forgetFutureHistory short long = short ++ fmap (second (const Nothing)) (short `dropBy` long)
