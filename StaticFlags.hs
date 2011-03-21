module StaticFlags where

import Data.Char (toLower)
import Data.Maybe
import Data.List (intercalate, stripPrefix)

import System.Environment
import System.IO.Unsafe
import System.Process


{-# NOINLINE aRGS #-}
aRGS :: [String]
aRGS = unsafePerformIO getArgs

{-# NOINLINE cODE_IDENTIFIER #-}
cODE_IDENTIFIER :: String
cODE_IDENTIFIER = head $ lines $ unsafePerformIO (readProcess "git" ["log", "--format=%H", "-1"] "")

rUN_IDENTIFIER :: String
rUN_IDENTIFIER = intercalate " " [filter (/= '-') arg | '-':'-':arg <- aRGS]

tIMEOUT_SECONDS :: Int
tIMEOUT_SECONDS = 120

tICKY :: Bool
tICKY = "--ticky" `elem` aRGS

nO_OPTIMISATIONS :: Bool
nO_OPTIMISATIONS = "-O0" `elem` aRGS

gHC_OPTIONS :: [String]
gHC_OPTIONS = [opt | arg <- aRGS, Just ('=':opt) <- [stripPrefix "--ghc-option" arg]]


aSSERTIONS :: Bool
aSSERTIONS = not $ "--no-assertions" `elem` aRGS

qUIET :: Bool
qUIET = "-v0" `elem` aRGS

rEDUCE_TERMINATION_CHECK :: Bool
rEDUCE_TERMINATION_CHECK = not $ "--no-reduce-termination" `elem` aRGS

eVALUATE_PRIMOPS :: Bool
eVALUATE_PRIMOPS = not $ "--no-primops" `elem` aRGS

dEEDS :: Bool
dEEDS = "--deeds" `elem` aRGS

parseEnum :: String -> a -> [(String, a)] -> a
parseEnum prefix def opts = fromMaybe def $ listToMaybe [parse opt | arg <- aRGS, Just ('=':opt) <- [stripPrefix prefix arg]]
  where parse = fromJust . flip lookup opts . map toLower

data DeedsPolicy = FCFS | Proportional
                 deriving (Read)

dEEDS_POLICY :: DeedsPolicy
dEEDS_POLICY = parseEnum "--deeds-policy" Proportional [("fcfs", FCFS), ("proportional", Proportional)]

data TagBagType = TBT { tagBagPairwiseGrowth :: Bool }
                deriving (Show)
data TagCollectionType = TagBag TagBagType | TagGraph | TagSet
                   deriving (Show)

tAG_COLLECTION :: TagCollectionType
tAG_COLLECTION = parseEnum "--tag-collection" (TagBag (TBT False)) [("bags", TagBag (TBT False)), ("bags-strong", TagBag (TBT True)), ("graphs", TagGraph), ("sets", TagSet)]

pARTITIONED_REFINEMENT :: Bool
pARTITIONED_REFINEMENT = "--partitioned-refinement" `elem` aRGS

sUB_GRAPHS :: Bool
sUB_GRAPHS = "--sub-graphs" `elem` aRGS

data GeneralisationType = NoGeneralisation | AllEligible | DependencyOrder Bool | StackFirst

gENERALISATION :: GeneralisationType
gENERALISATION = parseEnum "--generalisation" StackFirst [("none", NoGeneralisation), ("all-eligible", AllEligible), ("first-reachable", DependencyOrder True), ("last-reachable", DependencyOrder False), ("stack-first", StackFirst)]

bLOAT_FACTOR :: Int
bLOAT_FACTOR = fromMaybe 10 $ listToMaybe [read val | arg <- aRGS, Just val <- [stripPrefix "--bloat=" arg]]
 -- NB: need a bloat factor of at least 5 to get append/append fusion to work. The critical point is:
 --
 --  let (++) = ...
 --  in case (case xs of []     -> ys
 --                      (x:xs) -> x : (xs ++ ys)) of
 --    []     -> zs
 --    (x:xs) -> x : (xs ++ zs)
 --
 -- We need to duplicate the case continuation into each branch, so at one time we will have:
 --  1) Two copies of (++) in the [] branch of the inner case
 --    a) One in the heap
 --    b) One from the stack (from [_] ++ zs)
 --  2) Similarly two copies in the (:) branch of the inner case
 --  3) One copy manifested in the residual branch of xs
 --
 -- Total = 5 copies (due to tiebacks, the residual program will do better than this)
 --
 -- 
 -- Unfortunately, my implementation doesn't tie back as eagerly as you might like, so we actually peel the loop once and
 -- hence need a bloat factor of 8 here (5 + 3 other case statements derived from (++))
 -- TODO: figure out how to reduce this number.

sPECULATION :: Bool
sPECULATION = not $ "--no-speculation" `elem` aRGS

lOCAL_TIEBACKS :: Bool
lOCAL_TIEBACKS = "--local-tiebacks" `elem` aRGS

rEDUCE_ROLLBACK :: Bool
rEDUCE_ROLLBACK = not $ "--no-reduce-rollback" `elem` aRGS

sC_ROLLBACK :: Bool
sC_ROLLBACK = not $ "--no-sc-rollback" `elem` aRGS

dISCARD_FULFILMENTS_ON_ROLLBACK :: Bool
dISCARD_FULFILMENTS_ON_ROLLBACK = "--discard-fulfilments-on-rollback" `elem` aRGS

eXPAND_CASE_DEFAULTS :: Bool
eXPAND_CASE_DEFAULTS = "--expand-case-defaults" `elem` aRGS

eXPAND_CASE_UNCOVEREDS :: Bool
eXPAND_CASE_UNCOVEREDS = "--expand-case-uncovereds" `elem` aRGS

cALL_BY_NAME :: Bool
cALL_BY_NAME = "--call-by-name" `elem` aRGS

pRETTIFY :: Bool
pRETTIFY = "--prettify" `elem` aRGS

dUPLICATE_VALUES_EVALUATOR, dUPLICATE_VALUES_SPLITTER :: Bool
dUPLICATE_VALUES_EVALUATOR = "--duplicate-values-evaluator" `elem` aRGS
dUPLICATE_VALUES_SPLITTER = "--duplicate-values-splitter" `elem` aRGS

rEFINE_FULFILMENT_FVS :: Bool
rEFINE_FULFILMENT_FVS = not $ "--no-refine-fulfilment-fvs" `elem` aRGS

oCCURRENCE_GENERALISATION :: Bool
oCCURRENCE_GENERALISATION = not $ "--no-occurrence-generalisation" `elem` aRGS

mATCH_REDUCED :: Bool
mATCH_REDUCED = "--match-reduced" `elem` aRGS

mATCH_SPECULATION :: Bool
mATCH_SPECULATION = not $ "--no-match-speculation" `elem` aRGS

-- Turning this on is a really bad idea because it tells us how to generalise a *post reduced* term, but
-- we actually need to generalise a *pre-reduced* term. Oops!
rEDUCE_BEFORE_TEST :: Bool
rEDUCE_BEFORE_TEST = "--reduce-before-test" `elem` aRGS
