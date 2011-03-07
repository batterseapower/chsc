{-# LANGUAGE ViewPatterns #-}
module GHC where

import Core.Syntax

import Utilities
import StaticFlags

import Control.Exception

import System.Directory
import System.Exit
import System.IO
import System.Process


gHC :: FilePath
gHC = "/Users/mbolingbroke/Programming/Checkouts/ghc.head/inplace/bin/ghc-stage2"


termToHaskell :: Term -> String
termToHaskell = show . pPrintPrec haskellLevel 0

termToHaskellBinding :: String -> Term -> [String]
termToHaskellBinding name e = (name ++ " = " ++ l) : map (replicate indent ' ' ++) ls
  where indent = length name + 3
        (l:ls) = lines $ termToHaskell e

languageLine :: String
languageLine = "{-# LANGUAGE ExtendedDefaultRules, NoMonoPatBinds #-}"

testingModule :: String -> Term -> Term -> String
testingModule wrapper e test_e = unlines $
    languageLine :
    "module Main(main) where" :
    "import Data.Time.Clock.POSIX (getPOSIXTime)" :
    [wrapper] ++
    "" :
    "-- | A class of types that can be fully evaluated." :
    "class NFData a where" :
    "    rnf :: a -> ()" :
    "    rnf a = a `seq` ()" :
    "" :
    "instance NFData Int " :
    "instance NFData Integer" :
    "instance NFData Float" :
    "instance NFData Double" :
    "" :
    "instance NFData Char" :
    "instance NFData Bool" :
    "instance NFData ()" :
    "" :
    "instance NFData a => NFData (Maybe a) where" :
    "    rnf Nothing  = ()" :
    "    rnf (Just x) = rnf x" :
    "" :
    "instance (NFData a, NFData b) => NFData (Either a b) where" :
    "    rnf (Left x)  = rnf x" :
    "    rnf (Right y) = rnf y" :
    "" :
    "instance NFData a => NFData [a] where" :
    "    rnf [] = ()" :
    "    rnf (x:xs) = rnf x `seq` rnf xs" :
    "" :
    "instance (NFData a, NFData b) => NFData (a,b) where" :
    "  rnf (x,y) = rnf x `seq` rnf y" :
    "" :
    "time_ :: IO a -> IO Double" :
    "time_ act = do { start <- getTime; act; end <- getTime; return $! (Prelude.-) end start }" :
    "" :
    "getTime :: IO Double" :
    "getTime = (fromRational . toRational) `fmap` getPOSIXTime" :
    "" :
    "main = do { t <- time_ (rnf results `seq` return ()); print t }" :
    "  where results = map assertEq tests" :
    "" :
    "assertEq :: (Show a, Eq a) => (a, a) -> ()" :
    "assertEq (x, y) = if x == y then () else error (\"FAIL! \" ++ show x ++ \", \" ++ show y)" :
    "" :
    termToHaskellBinding "root" e ++
    termToHaskellBinding "tests" test_e

printingModule :: String -> Term -> String
printingModule wrapper e = unlines $
    languageLine :
    "module Main(main, root) where" :
    "import Text.Show.Functions" :
    [wrapper] ++
    "" :
    "main = print root" :
    "" :
    termToHaskellBinding "root" e



typechecks :: String -> Term -> IO Bool
typechecks wrapper term = do
    (ec, _out, err) <- withTempFile "Main.hs" $ \(file, h) -> do
        hPutStr h haskell
        hClose h
        readProcessWithExitCode gHC ["-c", file, "-fforce-recomp"] ""
    case ec of
      ExitSuccess -> return True
      _ -> do
        hPutStrLn stderr err
        return False
  where
    haskell = printingModule wrapper term

normalise :: String -> Term -> IO (Either String String)
normalise wrapper term = do
    let haskell = printingModule wrapper term
    (ec, out, err) <- withTempFile "Main.hs" $ \(file, h) -> do
        hPutStr h haskell
        hClose h
        readProcessWithExitCode gHC ["--make", "-O2", file, "-ddump-simpl", "-fforce-recomp"] ""
    case ec of
      ExitSuccess   -> return (Right out)
      ExitFailure _ -> hPutStrLn stderr haskell >> return (Left err)

ghcVersion :: IO [Int]
ghcVersion = do
    (ExitSuccess, compile_out, "") <- readProcessWithExitCode gHC ["--version"] ""
    return $ map read . seperate '.' . last . words $ compile_out

runCompiled :: String -> Term -> Term -> IO (String, Either String (Bytes, Seconds, Bytes, Seconds))
runCompiled wrapper e test_e = withTempFile "Main" $ \(exe_file, exe_h) -> do
    hClose exe_h
    let haskell = testingModule wrapper e test_e
    (compile_t, (ec, compile_out, compile_err)) <- withTempFile "Main.hs" $ \(hs_file, hs_h) -> do
        hPutStr hs_h haskell
        hClose hs_h
        ghc_ver <- ghcVersion
        time $ readProcessWithExitCode gHC (["--make", hs_file, "-fforce-recomp", "-o", exe_file] ++ [if nO_OPTIMISATIONS then "-O0" else "-O2"] ++ gHC_OPTIONS ++ ["-ddump-simpl" | not qUIET] ++ ["-ticky" | tICKY] ++ ["-rtsopts" | ghc_ver >= [7]]) ""
    compiled_size <- fileSize exe_file
    case ec of
      ExitFailure _ -> hPutStrLn stderr haskell >> return (haskell, Left compile_err)
      ExitSuccess   -> do
          (ec, run_out, run_err) <- readProcessWithExitCode exe_file (["+RTS", "-t"] ++ ["-rstderr" | tICKY]) ""
          case ec of
            ExitFailure _ -> hPutStrLn stderr haskell >> return (haskell, Left (unlines [compile_out, run_err]))
            ExitSuccess -> do
              -- <<ghc: 7989172 bytes, 16 GCs, 20876/20876 avg/max bytes residency (1 samples), 1M in use, 0.00 INIT (0.00 elapsed), 0.02 MUT (0.51 elapsed), 0.00 GC (0.00 elapsed) :ghc>>
              let [t_str] = lines run_out
                  [gc_stats] = (filter ("<<ghc" `isPrefixOf`) . lines) run_err
                  total_bytes_allocated = read (words gc_stats !! 1)
              return (haskell ++ unlines ["", "{-", run_err, "-}"], Right (compiled_size, compile_t, total_bytes_allocated, read t_str))

withTempFile :: String -> ((FilePath, Handle) -> IO b) -> IO b
withTempFile name action = do
    tmpdir <- getTemporaryDirectory
    bracket
        (openTempFile tmpdir name)
        (\(fp,h) -> hClose h >> removeFile fp)
        action
