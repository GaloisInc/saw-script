module Main where

import System.Environment (getArgs)
import System.IO (hFlush, stdout)

import SAWScript.Parser   (parse)

main :: IO ()
main = do putStrLn "Welcome to SAWScript!"
          as <- getArgs
          case as of
            []  -> testLoop
            fs  -> mapM_ processFile fs

testLoop :: IO ()
testLoop = do putStr "input? "
              hFlush stdout
              l <- getLine
              if null l
                 then return ()
                 else do process "stdin" l
                         testLoop

processFile :: FilePath -> IO ()
processFile f = do
    putStrLn $ "Reading " ++ show f ++ ".."
    cts <- readFile f
    process f cts

process :: FilePath -> String -> IO ()
process f s = do er <- parse f s
                 case er of
                   Left e  -> putStrLn $ "*** Error:" ++ e
                   Right r -> putStrLn $ show r
