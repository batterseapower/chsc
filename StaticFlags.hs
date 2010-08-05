module StaticFlags where

import Data.Maybe

import System.Environment
import System.IO.Unsafe


{-# NOINLINE aSSERTIONS #-}
aSSERTIONS :: Bool
aSSERTIONS = not $ "--no-assertions" `elem` unsafePerformIO getArgs

{-# NOINLINE qUIET #-}
qUIET :: Bool
qUIET = "-v0" `elem` unsafePerformIO getArgs

{-# NOINLINE tERMINATION_CHECK #-}
tERMINATION_CHECK :: Bool
tERMINATION_CHECK = not $ "--no-termination" `elem` unsafePerformIO getArgs

{-# NOINLINE eVALUATE_PRIMOPS #-}
eVALUATE_PRIMOPS :: Bool
eVALUATE_PRIMOPS = not $ "--no-primops" `elem` unsafePerformIO getArgs

{-# NOINLINE gENERALISATION #-}
gENERALISATION :: Bool
gENERALISATION = not $ "--no-generalisation" `elem` unsafePerformIO getArgs

{-# NOINLINE bLOAT_FACTOR #-}
bLOAT_FACTOR :: Int
bLOAT_FACTOR = fromMaybe 10 $ listToMaybe [read arg | '-':'-':'b':'l':'o':'a':'t':'=':arg <- unsafePerformIO getArgs]
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
 -- hence need a bloat factor of 10 here FIXME: figure out how to reduce this number.

{-# NOINLINE sPLITTER_CHEAPIFICATION #-}
sPLITTER_CHEAPIFICATION :: Bool
sPLITTER_CHEAPIFICATION = "--cheapification" `elem` unsafePerformIO getArgs
 -- TODO: test my hypothesis that given that we already do speculation, let-floating in the splitter won't make much difference

{-# NOINLINE sPECULATION #-}
sPECULATION :: Bool
sPECULATION = not $ "--no-speculation" `elem` unsafePerformIO getArgs

-- NB: may want to these definitions if you want to default speculation to off
    
-- {-# NOINLINE sPLITTER_CHEAPIFICATION #-}
-- sPLITTER_CHEAPIFICATION :: Bool
-- sPLITTER_CHEAPIFICATION = not $ "--no-cheapification" `elem` unsafePerformIO getArgs
-- 
-- {-# NOINLINE sPECULATION #-}
-- sPECULATION :: Bool
-- sPECULATION = "--speculation" `elem` unsafePerformIO getArgs

{-# NOINLINE sPECULATE_ON_LOSERS #-}
sPECULATE_ON_LOSERS :: Bool
sPECULATE_ON_LOSERS = "--speculate-on-losers" `elem` unsafePerformIO getArgs

{-# NOINLINE lOCAL_TIEBACKS #-}
lOCAL_TIEBACKS :: Bool
lOCAL_TIEBACKS = not $ "--no-local-tiebacks" `elem` unsafePerformIO getArgs

{-# NOINLINE rEDUCE_ROLLBACK #-}
rEDUCE_ROLLBACK :: Bool
rEDUCE_ROLLBACK = not $ "--no-reduce-rollback" `elem` unsafePerformIO getArgs
