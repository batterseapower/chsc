module StaticFlags where

import System.Environment
import System.IO.Unsafe


{-# NOINLINE aSSERTIONS #-}
aSSERTIONS :: Bool
aSSERTIONS = not $ "--no-assertions" `elem` (unsafePerformIO getArgs)

{-# NOINLINE qUIET #-}
qUIET :: Bool
qUIET = "-v0" `elem` (unsafePerformIO getArgs)

{-# NOINLINE tERMINATION_CHECK #-}
tERMINATION_CHECK :: Bool
tERMINATION_CHECK = not $ "--no-termination" `elem` (unsafePerformIO getArgs)

{-# NOINLINE eVALUATE_PRIMOPS #-}
eVALUATE_PRIMOPS :: Bool
eVALUATE_PRIMOPS = not $ "--no-primops" `elem` (unsafePerformIO getArgs)

{-# NOINLINE sPECULATION #-}
sPECULATION :: Bool
sPECULATION = not $ "--no-speculation" `elem` (unsafePerformIO getArgs)
