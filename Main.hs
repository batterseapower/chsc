{-# LANGUAGE ViewPatterns #-}
module Main (main) where

import Core.FreeVars
import Core.Syntax
import Core.Parser

import Supercompile.Drive

import GHC
import Name
import Utilities
import StaticFlags

import Data.Char (toLower)
import qualified Data.Set as S

import System.Directory
import System.Environment
import System.Exit
import System.FilePath ((</>), dropExtension, takeFileName, takeDirectory, replaceExtension)
import System.IO

import Numeric (showFFloat)


-- The Cambridge Haskell Supercompiler (CHSC)
main :: IO ()
main = do
    (_flags, args) <- fmap (partition ("-" `isPrefixOf`)) getArgs
    mapM_ testOne args


splitModule :: [(Var, Term)] -> (Term, Maybe Term)
splitModule xes = (letRec (transitiveInline (S.singleton root)) (var root),
                   fmap (\test -> letRec (filter ((/= root) . fst) $ transitiveInline (S.singleton test)) (var test)) mb_test)
  where
    findBinding what = fmap fst $ find ((== what) . name_string . fst) xes
    
    transitiveInline fvs
        | fvs == fvs' = need_xes
        | otherwise   = transitiveInline fvs'
      where
        need_xes = [(x, e) | (x, e) <- xes, x `S.member` fvs]
        fvs' = fvs `S.union` S.unions (map (termFreeVars . snd) need_xes)
    
    root    = expectJust "No root" $ findBinding "root"
    mb_test = findBinding "tests"


testOne :: FilePath -> IO ()
testOne file = do
    hPutStrLn stderr file
    (wrapper, binds) <- parse file
    case splitModule binds of
      (_, Nothing) -> hPutStrLn stderr "Skipping: no tests"
      (e, Just test_e) -> do
        (before_code, before_res) <- runCompiled wrapper e test_e
    
        -- Save a copy of the non-supercompiled code
        createDirectoryIfMissing True (takeDirectory $ "input" </> file)
        writeFile ("input" </> replaceExtension file ".hs") before_code
    
        (_before_size, before_compile_t, before_heap_size, before_run_t) <- catchLeft before_res
    
        rnf e `seq` return ()
        let e' = supercompile e
        super_t <- time_ (rnf e' `seq` return ())
    
        (after_code, after_res) <- runCompiled wrapper e' test_e
    
        -- Save a copy of the supercompiled code somewhere so I can consult it at my leisure
        let output_dir = foldl1 (</>) [ "output"
                                      , if eVALUATE_PRIMOPS then "primops"  else "no-primops"
                                      , if gENERALISATION   then "gen"      else "no-gen"
                                      , if sPECULATION      then "spec"     else "no-spec"
                                      , if rEDUCE_ROLLBACK  then "reducerb" else "no-reducerb"
                                      ]
        createDirectoryIfMissing True (takeDirectory $ output_dir </> file)
        writeFile (output_dir </> replaceExtension file ".hs") after_code
        
        (_after_size, after_compile_t, after_heap_size, after_run_t) <- catchLeft after_res
        
        let dp1 x = showFFloat (Just 1) x ""
            dp2 x = showFFloat (Just 2) x ""
            ratio n m = fromIntegral n / fromIntegral m :: Double
            escape = concatMap (\c -> if c == '_' then "\\_" else [c])
        putStrLn $ intercalate " & " [escape $ map toLower $ takeFileName $ dropExtension file, dp1 super_t ++ "s", dp2 (after_compile_t / before_compile_t), dp2 (after_run_t / before_run_t), dp2 (after_heap_size `ratio` before_heap_size)] ++ " \\\\"

catchLeft :: Either String b -> IO b
catchLeft (Left err)  = hPutStrLn stderr err >> exitWith (ExitFailure 1)
catchLeft (Right res) = return res
