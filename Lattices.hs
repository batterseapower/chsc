module Lattices (
        PartialOrd(..),
        partialOrdEq,
        
        JoinSemiLattice(..), MeetSemiLattice(..), Lattice,
        joinLeq, joins1, meetLeq, meets1,
        
        BoundedJoinSemiLattice(..), BoundedMeetSemiLattice(..), BoundedLattice,
        joins, meets,
        
        lfp, unsafeLfp, lfpFrom, unsafeLfpFrom,
        gfp, unsafeGfp, gfpFrom, unsafeGfpFrom
    ) where

import qualified Data.Set as S
import qualified Data.Map as M


-- | A partial ordering on sets: <http://en.wikipedia.org/wiki/Partially_ordered_set>
--
-- This can be defined using either |joinLeq| or |meetLeq|, or a more efficient definition
-- can be derived directly.
--
-- Reflexive:     a `leq` a
-- Antisymmetric: a `leq` b && b `leq` a ==> a == b
-- Transitive:    a `leq` b && b `leq` c ==> a `leq` c
--
-- The superclass equality (which can be defined using |partialOrdEq|) must obey these laws:
--
-- Reflexive:  a == a
-- Transitive: a == b && b == c ==> a == b
class Eq a => PartialOrd a where
    leq :: a -> a -> Bool

-- | The equality relation induced by the partial-order structure
partialOrdEq :: PartialOrd a => a -> a -> Bool
partialOrdEq x y = leq x y && leq y x


-- | A algebraic structure with element joins: <http://en.wikipedia.org/wiki/Semilattice>
--
-- Associativity: x `join` (y `join` z) == (x `join` y) `join` z
-- Commutativity: x `join` y == y `join` x
-- Idempotency:   x `join` x == x
class JoinSemiLattice a where
    join :: a -> a -> a

-- | The partial ordering induced by the join-semilattice structure
joinLeq :: (Eq a, JoinSemiLattice a) => a -> a -> Bool
joinLeq x y = x `join` y == y

-- | The join of at a list of join-semilattice elements (of length at least one)
joins1 :: JoinSemiLattice a => [a] -> a
joins1 = foldr1 join

-- | A algebraic structure with element meets: <http://en.wikipedia.org/wiki/Semilattice>
--
-- Associativity: x `meet` (y `meet` z) == (x `meet` y) `meet` z
-- Commutativity: x `meet` y == y `meet` x
-- Idempotency:   x `meet` x == x
class MeetSemiLattice a where
    meet :: a -> a -> a

-- | The partial ordering induced by the meet-semilattice structure
meetLeq :: (Eq a, MeetSemiLattice a) => a -> a -> Bool
meetLeq x y = x `meet` y == x

-- | The meet of at a list of meet-semilattice elements (of length at least one)
meets1 :: MeetSemiLattice a => [a] -> a
meets1 = foldr1 meet

-- | The combination of two semi lattices makes a lattice if the absorption law holds:
-- see <http://en.wikipedia.org/wiki/Absorption_law> and <http://en.wikipedia.org/wiki/Lattice_(order)>
--
-- Absorption: a `join` (a `meet` b) == a `meet` (a `join` b) == a
class (JoinSemiLattice a, MeetSemiLattice a) => Lattice a where

-- | A join-semilattice with some element |bottom| that `join` approaches.
--
-- Identity: x `join` bottom == x
class JoinSemiLattice a => BoundedJoinSemiLattice a where
    bottom :: a

-- | The join of a list of join-semilattice elements
joins :: BoundedJoinSemiLattice a => [a] -> a
joins = foldr join bottom

-- | A meet-semilattice with some element |top| that `meet` approaches.
--
-- Identity: x `meet` top == x
class MeetSemiLattice a => BoundedMeetSemiLattice a where
    top :: a

-- | The meet of a list of meet-semilattice elements
meets :: BoundedMeetSemiLattice a => [a] -> a
meets = foldr meet top


-- | Lattices with both bounds
class (Lattice a, BoundedJoinSemiLattice a, BoundedMeetSemiLattice a) => BoundedLattice a where


instance Ord a => PartialOrd (S.Set a) where
    leq = S.isSubsetOf

instance Ord a => JoinSemiLattice (S.Set a) where
    join = S.union

instance (Ord a, Enum a, Bounded a) => MeetSemiLattice (S.Set a) where
    meet = S.intersection

instance (Ord a, Enum a, Bounded a) => Lattice (S.Set a) where

instance Ord a => BoundedJoinSemiLattice (S.Set a) where
    bottom = S.empty

instance (Ord a, Enum a, Bounded a) => BoundedMeetSemiLattice (S.Set a) where
    top = S.fromList (enumFromTo minBound maxBound)

instance (Ord a, Enum a, Bounded a) => BoundedLattice (S.Set a) where


instance (Ord k, PartialOrd v) => PartialOrd (M.Map k v) where
    leq = M.isSubmapOf

instance (Ord k, JoinSemiLattice v) => JoinSemiLattice (M.Map k v) where
    join = M.unionWith join

instance (Ord k, Enum k, Bounded k, MeetSemiLattice v) => MeetSemiLattice (M.Map k v) where
    meet = M.intersectionWith meet

instance (Ord k, Enum k, Bounded k, Lattice v) => Lattice (M.Map k v) where

instance (Ord k, JoinSemiLattice v) => BoundedJoinSemiLattice (M.Map k v) where
    bottom = M.empty

instance (Ord k, Enum k, Bounded k, BoundedMeetSemiLattice v) => BoundedMeetSemiLattice (M.Map k v) where
    top = M.fromList (enumFromTo minBound maxBound `zip` repeat top)

instance (Ord k, Enum k, Bounded k, BoundedLattice v) => BoundedLattice (M.Map k v) where


instance (Enum k, Bounded k, Eq v) => Eq (k -> v) where
    f == g = all (\k -> f k == g k) (enumFromTo minBound maxBound)

instance (Enum k, Bounded k, PartialOrd v) => PartialOrd (k -> v) where
    f `leq` g = all (\k -> f k `leq` g k) (enumFromTo minBound maxBound)

instance JoinSemiLattice v => JoinSemiLattice (k -> v) where
    f `join` g = \x -> f x `join` g x

instance MeetSemiLattice v => MeetSemiLattice (k -> v) where
    f `meet` g = \x -> f x `meet` g x

instance Lattice v => Lattice (k -> v) where

instance BoundedJoinSemiLattice v => BoundedJoinSemiLattice (k -> v) where
    bottom = const bottom

instance BoundedMeetSemiLattice v => BoundedMeetSemiLattice (k -> v) where
    top = const top

instance BoundedLattice v => BoundedLattice (k -> v) where


instance (PartialOrd a, PartialOrd b) => PartialOrd (a, b) where
    -- NB: *not* a lexical ordering. This is because for some component partial orders, lexical
    -- ordering is incompatible with the transitivity axiom we require for the derived partial order
    (x1, y1) `leq` (x2, y2) = x1 `leq` x2 && y1 `leq` y2

instance (JoinSemiLattice a, JoinSemiLattice b) => JoinSemiLattice (a, b) where
    (x1, y1) `join` (x2, y2) = (x1 `join` x2, y1 `join` y2)

instance (MeetSemiLattice a, MeetSemiLattice b) => MeetSemiLattice (a, b) where
    (x1, y1) `meet` (x2, y2) = (x1 `meet` x2, y1 `meet` y2)

instance (Lattice a, Lattice b) => Lattice (a, b) where

instance (BoundedJoinSemiLattice a, BoundedJoinSemiLattice b) => BoundedJoinSemiLattice (a, b) where
    bottom = (bottom, bottom)

instance (BoundedMeetSemiLattice a, BoundedMeetSemiLattice b) => BoundedMeetSemiLattice (a, b) where
    top = (top, top)

instance (BoundedLattice a, BoundedLattice b) => BoundedLattice (a, b) where


-- | Least point of a partially ordered monotone function. Checks that the function is monotone.
lfpFrom :: PartialOrd a => a -> (a -> a) -> a
lfpFrom = lfpFrom' leq

-- | Least point of a partially ordered monotone function. Does not checks that the function is monotone.
unsafeLfpFrom :: Eq a => a -> (a -> a) -> a
unsafeLfpFrom = lfpFrom' (\_ _ -> True)

{-# INLINE lfpFrom' #-}
lfpFrom' :: Eq a => (a -> a -> Bool) -> a -> (a -> a) -> a
lfpFrom' check init_x f = go init_x
  where go x | x' == x      = x
             | x `check` x' = go x'
             | otherwise    = error "lfpFrom: non-monotone function"
          where x' = f x

-- | Implementation of Kleene fixed-point theorem <http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem>.
-- Assumes that the function is monotone and does not check if that is correct.
{-# INLINE unsafeLfp #-}
unsafeLfp :: (Eq a, BoundedJoinSemiLattice a) => (a -> a) -> a
unsafeLfp = unsafeLfpFrom bottom

-- | Implementation of Kleene fixed-point theorem <http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem>.
-- Forces the function to be monotone.
{-# INLINE lfp #-}
lfp :: (Eq a, BoundedJoinSemiLattice a) => (a -> a) -> a
lfp f = unsafeLfpFrom bottom (\x -> f x `join` x)


-- | Greatest fixed point of a partially ordered antinone function. Checks that the function is antinone.
{-# INLINE gfpFrom #-}
gfpFrom :: PartialOrd a => a -> (a -> a) -> a
gfpFrom = gfpFrom' leq

-- | Greatest fixed point of a partially ordered antinone function. Does not check that the function is antinone.
{-# INLINE unsafeGfpFrom #-}
unsafeGfpFrom :: Eq a => a -> (a -> a) -> a
unsafeGfpFrom = gfpFrom' (\_ _ -> True)

{-# INLINE gfpFrom' #-}
gfpFrom' :: Eq a => (a -> a -> Bool) -> a -> (a -> a) -> a
gfpFrom' check init_x f = go init_x
  where go x | x' == x      = x
             | x' `check` x = go x'
             | otherwise    = error "gfpFrom: non-antinone function"
          where x' = f x

-- | Implementation of Kleene fixed-point theorem <http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem>.
-- Assumes that the function is antinone and does not check if that is correct.
{-# INLINE unsafeGfp #-}
unsafeGfp :: (Eq a, BoundedMeetSemiLattice a) => (a -> a) -> a
unsafeGfp = unsafeGfpFrom top

-- | Implementation of Kleene fixed-point theorem <http://en.wikipedia.org/wiki/Kleene_fixed-point_theorem>.
-- Forces the function to be antinone.
{-# INLINE gfp #-}
gfp :: (Eq a, BoundedMeetSemiLattice a) => (a -> a) -> a
gfp f = unsafeGfpFrom top (\x -> f x `meet` x)
