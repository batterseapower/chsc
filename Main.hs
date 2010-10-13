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


type Ways = (Bool, Bool)


-- The Cambridge Haskell Supercompiler (CHSC)
main :: IO ()
main = do
    (flags, args) <- fmap (partition ("-" `isPrefixOf`)) getArgs
    putStrLn $ intercalate " " flags
    case args of
      []            -> putStrLn "TODO: usage"
      ("ghc":files) -> test (True,  False) files
      ("raw":files) -> test (False, True)  files
      files         -> test (True,  True)  files

test :: Ways -> [FilePath] -> IO ()
test ways files = do
    putStrLn $ intercalate " & " ["Filename", "SC time", "Compile time", "Run time", "Heap size", "Term size"] ++ " \\\\"
    mapM_ (testOne ways) files

splitModule :: [(Var, Term)] -> (Term, Maybe Term)
splitModule xes = (letRecSmart (transitiveInline (S.singleton root)) (var root),
                   fmap (\test -> letRecSmart (filter ((/= root) . fst) $ transitiveInline (S.singleton test)) (var test)) mb_test)
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


testOne :: Ways -> FilePath -> IO ()
testOne (ghc_way, sc_way) file = do
    hPutStrLn stderr $ "% " ++ file
    (wrapper, binds) <- parse file
    case splitModule binds of
      (_, Nothing) -> hPutStrLn stderr "Skipping: no tests"
      (e, Just test_e) -> do
        mb_before <- if not ghc_way
                     then return Nothing
                     else fmap Just $ do
                       (before_code, before_res) <- runCompiled wrapper e test_e
                       
                       -- Save a copy of the non-supercompiled code
                       createDirectoryIfMissing True (takeDirectory $ "input" </> file)
                       writeFile ("input" </> replaceExtension file ".hs") before_code
                       
                       fmap (,termSize e,Nothing) $ catchLeft before_res
    
        mb_after <- if not sc_way
                    then return Nothing
                    else fmap Just $ do
                      rnf e `seq` return ()
                      let e' = supercompile e
                      super_t <- time_ (rnf e' `seq` return ())
                      
                      (after_code, after_res) <- runCompiled wrapper e' test_e
                      
                      -- Save a copy of the supercompiled code somewhere so I can consult it at my leisure
                      let output_dir = "output" </> cODE_IDENTIFIER </> rUN_IDENTIFIER
                      createDirectoryIfMissing True (takeDirectory $ output_dir </> file)
                      writeFile (output_dir </> replaceExtension file ".hs") after_code
                      
                      fmap (,termSize e',Just super_t) $ catchLeft after_res
    
        let benchmark = escape $ map toLower $ takeFileName $ dropExtension file
            dp1 x = showFFloat (Just 1) x ""
            dp2 x = showFFloat (Just 2) x ""
            ratio n m = fromIntegral n / fromIntegral m :: Double
            escape = concatMap (\c -> if c == '_' then "\\_" else [c])
        case (mb_before, mb_after) of
          (Just ((_before_size, before_compile_t, before_heap_size, before_run_t), before_term_size, Nothing),
           Just ((_after_size,  after_compile_t,  after_heap_size,  after_run_t),  after_term_size,  Just after_super_t))
            -> putStrLn $ intercalate " & " [benchmark, dp1 after_super_t ++ "s", dp2 (after_compile_t / before_compile_t), dp2 (after_run_t / before_run_t), dp2 (after_heap_size `ratio` before_heap_size), dp2 (after_term_size `ratio` before_term_size)] ++ " \\\\"
          _ -> case mb_before `mplus` mb_after of Just ((size, compile_t, heap_size, run_t), term_size, mb_super_t) ->
                 putStrLn $ intercalate " & " [benchmark, maybe "" show mb_super_t, show compile_t, show run_t, show heap_size, show term_size] ++ " \\\\"

catchLeft :: Either String b -> IO b
catchLeft (Left err)  = hPutStrLn stderr err >> exitWith (ExitFailure 1)
catchLeft (Right res) = return res
