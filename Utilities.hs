{-# LANGUAGE TupleSections, PatternGuards, ExistentialQuantification, DeriveFunctor,
             FlexibleInstances, IncoherentInstances, OverlappingInstances, TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Utilities (
    module IdSupply,
    module Utilities,
    
    module Control.Arrow,
    module Control.DeepSeq,
    module Control.Monad,
    
    module Data.Maybe,
    module Data.List,
    
    module Debug.Trace,
    
    module Text.PrettyPrint.HughesPJClass
  ) where

import IdSupply
import StaticFlags

import Control.Arrow (first, second, (***), (&&&))
import Control.DeepSeq (NFData(..), rnf)
import Control.Monad hiding (join)

import Data.Maybe
import Data.Monoid
import Data.List
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Tree
import Data.Time.Clock.POSIX (getPOSIXTime)
import qualified Data.Foldable as Foldable
import qualified Data.Traversable as Traversable

import Debug.Trace

import Text.PrettyPrint.HughesPJClass hiding (render, int, char)
import qualified Text.PrettyPrint.HughesPJClass as Pretty

import System.IO
import System.IO.Unsafe (unsafePerformIO)


instance Monad (Either a) where
    return = Right
    
    Left l  >>= _    = Left l
    Right x >>= fxmy = fxmy x


class Show1 f where
    showsPrec1 :: Show a => Int -> f a -> ShowS

instance (Show1 f, Show a) => Show (f a) where
    showsPrec = showsPrec1


class Eq1 f where
    eq1 :: Eq a => f a -> f a -> Bool

instance (Eq1 f, Eq a) => Eq (f a) where
    (==) = eq1


class Eq1 f => Ord1 f where
    compare1 :: Ord a => f a -> f a -> Ordering

instance (Ord1 f, Ord a) => Ord (f a) where
    compare = compare1


class NFData1 f where
    rnf1 :: NFData a => f a -> ()

instance (NFData1 f, NFData a) => NFData (f a) where
    rnf = rnf1


class Pretty1 f where
    pPrintPrec1 :: Pretty a => PrettyLevel -> Rational -> f a -> Doc

instance (Pretty1 f, Pretty a) => Pretty (f a) where
    pPrintPrec = pPrintPrec1


instance NFData Id where
    rnf i = rnf (hashedId i)


data Counted a = Counted { count :: Int, countee :: a }

instance Show1 Counted where
    showsPrec1 prec (Counted c x) = showParen (prec >= appPrec) (showString "Counted" . showsPrec appPrec c . showsPrec appPrec x)

instance Eq1 Counted where
    eq1 (Counted c1 x1) (Counted c2 x2) = c1 == c2 && x1 == x2

instance Ord1 Counted where
    compare1 (Counted c1 x1) (Counted c2 x2) = (c1, x1) `compare` (c2, x2)

instance NFData1 Counted where
    rnf1 (Counted a b) = rnf a `seq` rnf b

instance Pretty1 Counted where
    pPrintPrec1 level _prec (Counted count x) = text ("[" ++ show count ++ "]") <> pPrintPrec level appPrec x

instance Functor Counted where
    fmap f (Counted c x) = Counted c (f x)


newtype (f :.: g) a = Comp { unComp :: f (g a) }

instance (Show1 f, Show1 g) => Show1 (f :.: g) where
    showsPrec1 prec (Comp x) = showParen (prec >= appPrec) (showString "Comp" . showsPrec appPrec x)

instance (Eq1 f, Eq1 g) => Eq1 (f :.: g) where
    eq1 (Comp x1) (Comp x2) = x1 == x2

instance (Ord1 f, Ord1 g) => Ord1 (f :.: g) where
    compare1 (Comp x1) (Comp x2) = x1 `compare` x2

instance (NFData1 f, NFData1 g) => NFData1 (f :.: g) where
    rnf1 (Comp x) = rnf x

instance (Pretty1 f, Pretty1 g) => Pretty1 (f :.: g) where
    pPrintPrec1 level prec (Comp x) = pPrintPrec level prec x

instance (Functor f, Functor g) => Functor (f :.: g) where
    fmap f (Comp x) = Comp (fmap (fmap f) x)


type Tag = Int

injectTag :: Int -> Tag -> Tag
injectTag cls tg = cls * tg

data Tagged a = Tagged { tag :: !Tag, tagee :: !a }

instance Show1 Tagged where
    showsPrec1 prec (Tagged tg x) = showParen (prec >= appPrec) (showString "Tagged" . showsPrec appPrec tg . showsPrec appPrec x)

instance Eq1 Tagged where
    eq1 (Tagged tg1 x1) (Tagged tg2 x2) = tg1 == tg2 && x1 == x2

instance Ord1 Tagged where
    compare1 (Tagged tg1 x1) (Tagged tg2 x2) = (tg1, x1) `compare` (tg2, x2)

instance NFData1 Tagged where
    rnf1 (Tagged a b) = rnf a `seq` rnf b

instance Pretty1 Tagged where
    pPrintPrec1 level prec (Tagged tg x) = braces (pPrint tg) <+> pPrintPrec level prec x

instance Functor Tagged where
    fmap f (Tagged tg x) = Tagged tg (f x)


instance Show IdSupply where
    show = show . idFromSupply


instance Pretty Doc where
    pPrint = id

instance Pretty Id where
    pPrint = text . show

instance Pretty a => Pretty (S.Set a) where
    pPrint xs = braces $ hsep (punctuate comma (map pPrint $ S.toList xs))

instance (Pretty k, Pretty v) => Pretty (M.Map k v) where
    pPrint m = brackets $ fsep (punctuate comma [pPrint k <+> text "|->" <+> pPrint v | (k, v) <- M.toList m])

instance Pretty a => Pretty (Tree a) where
    pPrint = text . drawTree . fmap (show . pPrint)

deleteList :: Ord a => [a] -> S.Set a -> S.Set a
deleteList = flip $ foldr S.delete

fmapSet :: (Ord a, Ord b) => (a -> b) -> S.Set a -> S.Set b
fmapSet f = S.fromList . map f . S.toList

fmapMap :: (Ord a, Ord b) => (a -> b) -> M.Map a v -> M.Map b v
fmapMap f = M.fromList . map (first f) . M.toList

restrict :: Ord k => M.Map k v -> S.Set k -> M.Map k v
restrict m s = M.filterWithKey (\k _ -> k `S.member` s) m

exclude :: Ord k => M.Map k v -> S.Set k -> M.Map k v
exclude m s = M.filterWithKey (\k _ -> k `S.notMember` s) m

mapMaybeSet :: (Ord a, Ord b) => (a -> Maybe b) -> S.Set a -> S.Set b
mapMaybeSet f = S.fromList . mapMaybe f . S.toList

setToMap :: Ord k => v -> S.Set k -> M.Map k v
setToMap v = M.fromAscList . map (,v) . S.toAscList


{-# NOINLINE parseIdSupply #-}
parseIdSupply :: IdSupply
parseIdSupply = unsafePerformIO $ initIdSupply 'a'

{-# NOINLINE reduceIdSupply #-}
reduceIdSupply :: IdSupply
reduceIdSupply = unsafePerformIO $ initIdSupply 'u'

{-# NOINLINE tagIdSupply #-}
tagIdSupply :: IdSupply
tagIdSupply = unsafePerformIO $ initIdSupply 't'

{-# NOINLINE prettyIdSupply #-}
prettyIdSupply :: IdSupply
prettyIdSupply = unsafePerformIO $ initIdSupply 'p'

{-# NOINLINE matchIdSupply #-}
matchIdSupply :: IdSupply
matchIdSupply = unsafePerformIO $ initIdSupply 'm'

stepIdSupply :: IdSupply -> (IdSupply, Id)
stepIdSupply = second idFromSupply . splitIdSupply


data Train a b = Wagon a (Train a b)
               | Caboose b


appPrec, opPrec, noPrec :: Num a => a
appPrec = 2    -- Argument of a function application
opPrec  = 1    -- Argument of an infix operator
noPrec  = 0    -- Others

normalLevel, haskellLevel :: PrettyLevel
normalLevel = PrettyLevel 0
haskellLevel = PrettyLevel 1


angles, coangles :: Doc -> Doc
angles d = Pretty.char '<' <> d <> Pretty.char '>'
coangles d = Pretty.char '>' <> d <> Pretty.char '<'


pPrintPrec' :: Pretty a => a -> PrettyLevel -> Rational -> Doc
pPrintPrec' x level prec = pPrintPrec level prec x

-- NB: this render function is exported instead of the one from the library
render :: Doc -> String
render = renderStyle (style { lineLength = 120 })

pPrintRender :: Pretty a => a -> String
pPrintRender = render . pPrint

panic :: String -> Doc -> a
panic s d = error $ s ++ ": " ++ render d


traceRender :: Pretty a => a -> b -> b
traceRender x | qUIET     = id
              | otherwise = trace (pPrintRender x)

assertRender :: Pretty a => a -> Bool -> b -> b
assertRender _ _ x | not aSSERTIONS = x
assertRender _ True  x = x
assertRender a False _ = error (pPrintRender a)


removeOnes :: [a] -> [[a]]
removeOnes [] = []
removeOnes (x:xs) = xs : map (x:) (removeOnes xs)

listContexts :: [a] -> [([a], a, [a])]
listContexts xs = zipWith (\is (t:ts) -> (is, t, ts)) (inits xs) (init (tails xs))

bagContexts :: [a] -> [(a, [a])]
bagContexts xs = [(x, is ++ ts) | (is, x, ts) <- listContexts xs]


accumL :: (acc -> (acc, a)) -> acc -> Int -> (acc, [a])
accumL f = go
  where
    go acc n | n <= 0            = (acc, []) 
             | (acc, x) <- f acc = second (x:) (go acc (n - 1))


instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i) => Pretty (a, b, c, d, e, f, g, h, i) where
    pPrint (a, b, c, d, e, f, g, h, i)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i]

instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j) => Pretty (a, b, c, d, e, f, g, h, i, j) where
    pPrint (a, b, c, d, e, f, g, h, i, j)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j]

instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j, Pretty k) => Pretty (a, b, c, d, e, f, g, h, i, j, k) where
    pPrint (a, b, c, d, e, f, g, h, i, j, k)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j, pPrint k]

instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j, Pretty k, Pretty l) => Pretty (a, b, c, d, e, f, g, h, i, j, k, l) where
    pPrint (a, b, c, d, e, f, g, h, i, j, k, l)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j, pPrint k, pPrint l]

instance (Pretty a, Pretty b, Pretty c, Pretty d,
          Pretty e, Pretty f, Pretty g, Pretty h,
          Pretty i, Pretty j, Pretty k, Pretty l,
          Pretty m, Pretty n, Pretty o) => Pretty (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o) where
    pPrint (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
      = pPrintTuple [pPrint a, pPrint b, pPrint c, pPrint d,
                     pPrint e, pPrint f, pPrint g, pPrint h,
                     pPrint i, pPrint j, pPrint k, pPrint l,
                     pPrint m, pPrint n, pPrint o]

pPrintTuple :: [Doc] -> Doc
pPrintTuple ds = parens $ fsep $ punctuate comma ds


data SomePretty = forall a. Pretty a => SomePretty a

instance Pretty SomePretty where
    pPrintPrec level prec (SomePretty x) = pPrintPrec level prec x


newtype PrettyFunction = PrettyFunction (PrettyLevel -> Rational -> Doc)

instance Pretty PrettyFunction where
    pPrintPrec level prec (PrettyFunction f) = f level prec

asPrettyFunction :: Pretty a => a -> PrettyFunction
asPrettyFunction = PrettyFunction . pPrintPrec'


fst3 :: (a, b, c) -> a
fst3 (a, _, _) = a

snd3 :: (a, b, c) -> b
snd3 (_, b, _) = b

thd3 :: (a, b, c) -> c
thd3 (_, _, c) = c

first3 :: (a -> d) -> (a, b, c) -> (d, b, c)
first3 f (a, b, c) = (f a, b, c)

second3 :: (b -> d) -> (a, b, c) -> (a, d, c)
second3 f (a, b, c) = (a, f b, c)

third3 :: (c -> d) -> (a, b, c) -> (a, b, d)
third3 f (a, b, c) = (a, b, f c)

second4 :: (b -> e) -> (a, b, c, d) -> (a, e, c, d)
second4 f (a, b, c, d) = (a, f b, c, d)

third4 :: (c -> e) -> (a, b, c, d) -> (a, b, e, d)
third4 f (a, b, c, d) = (a, b, f c, d)

secondM :: Monad m => (b -> m c) -> (a, b) -> m (a, c)
secondM f (a, b) = liftM (a,) $ f b


uncurry3 :: (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c


splitBy :: [b] -> [a] -> ([a], [a])
splitBy []     xs     = ([], xs)
splitBy (_:ys) (x:xs) = first (x:) $ splitBy ys xs

splitManyBy :: [[b]] -> [a] -> [[a]]
splitManyBy []       xs = [xs]
splitManyBy (ys:yss) xs = case splitBy ys xs of (xs1, xs2) -> xs1 : splitManyBy yss xs2

dropBy :: [b] -> [a] -> [a]
dropBy bs = snd . splitBy bs


orElse :: Maybe a -> a -> a
orElse = flip fromMaybe


takeFirst :: (a -> Bool) -> [a] -> (Maybe a, [a])
takeFirst p = takeFirstJust (\x -> guard (p x) >> return x)

takeFirstJust :: (a -> Maybe b) -> [a] -> (Maybe b, [a])
takeFirstJust _ [] = (Nothing, [])
takeFirstJust p (x:xs)
  | Just y <- p x = (Just y, xs)
  | otherwise     = second (x:) $ takeFirstJust p xs

expectJust :: String -> Maybe a -> a
expectJust _ (Just x) = x
expectJust s Nothing  = error $ "expectJust: " ++ s

safeFromLeft :: Either a b -> Maybe a
safeFromLeft (Left x) = Just x
safeFromLeft _        = Nothing

safeHead :: [a] -> Maybe a
safeHead []    = Nothing
safeHead (x:_) = Just x

expectHead :: String -> [a] -> a
expectHead s = expectJust s . safeHead

uncons :: [a] -> Maybe (a, [a])
uncons []     = Nothing
uncons (x:xs) = Just (x, xs)

fixpoint :: Eq a => (a -> a) -> a -> a
fixpoint f x
   | x' == x   = x
   | otherwise = fixpoint f x'
  where x' = f x

zipWithEqualM :: Monad m => (a -> b -> m c) -> [a] -> [b] -> m [c]
zipWithEqualM _ []     []     = return []
zipWithEqualM f (x:xs) (y:ys) = liftM2 (:) (f x y) (zipWithEqualM f xs ys)
zipWithEqualM _ _ _ = fail "zipWithEqualM"

zipWithEqualM_ :: Monad m => (a -> b -> m ()) -> [a] -> [b] -> m ()
zipWithEqualM_ _ []     []     = return ()
zipWithEqualM_ f (x:xs) (y:ys) = f x y >> zipWithEqualM_ f xs ys
zipWithEqualM_ _ _ _ = fail "zipWithEqualM_"

zipWithEqual :: (a -> b -> c) -> [a] -> [b] -> Maybe [c]
zipWithEqual _ []     []     = Just []
zipWithEqual f (x:xs) (y:ys) = fmap (f x y :) $ zipWithEqual f xs ys
zipWithEqual _ _ _ = fail "zipWithEqual"

implies :: Bool -> Bool -> Bool
implies cond consq = not cond || consq


mapAccumM :: (Traversable.Traversable t, Monoid m) => (a -> (m, b)) -> t a -> (m, t b)
mapAccumM f ta = Traversable.mapAccumL (\m a -> case f a of (m', b) -> (m `mappend` m', b)) mempty ta


newtype Identity a = I { unI :: a } deriving (Functor)

instance Show1 Identity where
    showsPrec1 prec (I x) = showParen (prec >= appPrec) (showString "Identity" . showsPrec appPrec x)

instance Eq1 Identity where
    eq1 (I x1) (I x2) = x1 == x2

instance Ord1 Identity where
    compare1 (I x1) (I x2) = x1 `compare` x2

instance NFData1 Identity where
    rnf1 (I x) = rnf x

instance Pretty1 Identity where
    pPrintPrec1 level prec (I x) = pPrintPrec level prec x

instance Monad Identity where
    return = I
    mx >>= fxmy = fxmy (unI mx)


class (Functor t, Foldable.Foldable t) => Accumulatable t where
    mapAccumT  ::            (acc -> x ->   (acc, y)) -> acc -> t x ->   (acc, t y)
    mapAccumTM :: Monad m => (acc -> x -> m (acc, y)) -> acc -> t x -> m (acc, t y)
    
    mapAccumT f acc x = unI (mapAccumTM (\acc' x' -> I (f acc' x')) acc x)

fmapDefault :: (Accumulatable t) => (a -> b) -> t a -> t b
fmapDefault f = snd . mapAccumT (\() x -> ((), f x)) ()

foldMapDefault :: (Accumulatable t, Monoid m) => (a -> m) -> t a -> m
foldMapDefault f = fst . mapAccumT (\acc x -> (f x `mappend` acc, ())) mempty

instance Accumulatable [] where
    mapAccumT  = mapAccumL
    mapAccumTM = mapAccumLM

mapAccumLM :: Monad m => (acc -> x -> m (acc, y)) -> acc -> [x] -> m (acc, [y])
mapAccumLM f = go []
  where
    go ys acc []     = return (acc, reverse ys)
    go ys acc (x:xs) = do
      (acc, y) <- f acc x
      go (y:ys) acc xs

instance Ord k => Accumulatable (M.Map k) where
    mapAccumTM f acc = liftM (second M.fromList) . mapAccumTM (\acc (k, x) -> liftM (second (k,)) (f acc x)) acc . M.toList


type Seconds = Double

time_ :: IO a -> IO Seconds
time_ = fmap fst . time

time :: IO a -> IO (Seconds, a)
time act = do { start <- getTime; res <- act; end <- getTime; return (end - start, res) }

getTime :: IO Seconds
getTime = (fromRational . toRational) `fmap` getPOSIXTime


type Bytes = Integer

fileSize :: FilePath -> IO Bytes
fileSize file = withFile file ReadMode hFileSize
