{-# LANGUAGE PatternGuards, ViewPatterns, Rank2Types, TupleSections, GADTs, DeriveFunctor, DeriveFoldable, ScopedTypeVariables, TypeSynonymInstances, GeneralizedNewtypeDeriving #-}
module Termination.Terminate4 (
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


-- newtype Vec n a = UnsafeCertifyVecLength { unVec :: [a] }
--                 deriving (Functor, Foldable.Foldable, Traversable.Traversable)
-- 
-- instance Zippable (Vec n) where
--     zipWith_ f (UnsafeCertifyVecLength xs) (UnsafeCertifyVecLength ys) = UnsafeCertifyVecLength (zipWith f xs ys)


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

newtype History a why = History { terminate :: a -> TermRes a why }

data TermRes a why = Stop why | Continue (History a why)

isContinue :: TermRes a why -> Bool
isContinue (Continue _) = True
isContinue _ = False

{-# INLINE mkHistory #-}
mkHistory :: forall a why. WQO a why -> History a why
mkHistory (WQO (prepare :: a -> repr) embed) = History $ go []
  where
    go :: [repr] -> a -> TermRes a why
    go seen (prepare -> here)
      -- | traceRender (length seen, tagBag here) && False = undefined
      | why:_ <- [why | prev <- seen, Just why <- [prev `embed` here]]
      = Stop why
      | otherwise
      = Continue $ History $ go (here : seen)
