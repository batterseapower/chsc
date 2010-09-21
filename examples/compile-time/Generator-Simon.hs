#!/usr/bin/env runhaskell

import System.Environment

main :: IO ()
main = do
    [n_s] <- getArgs
    mapM_ putStrLn $ build (read n_s)

build :: Int -> [String]
build n = [
    "root = f1 0",
    ""
  ] ++ concatMap f [1..n-1] ++ [
    "f" ++ show n ++ " x = [x `add'Int` 1]",
    "",
    "(++) xs ys = case xs of",
    "    [] -> ys",
    "    (z:zs) -> z : (zs ++ ys)",
    "",
    "null xs = case xs of [] -> True; (y:ys) -> False",
    "",
    "tests = [",
    "    (null root, False)",
    "  ]"
  ]

f :: Int -> [String]
f n = [
    "f" ++ show n ++ " x = f" ++ show (n `add'Int` 1) ++ " y ++ f"  ++ show (n `add'Int` 1) ++ " (y `add'Int` 1)",
    "  where y = (x `add'Int` 1) * 2"
  ]