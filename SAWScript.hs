module Main where

import SAWScript.MethodAST
import SAWScript.SAWScriptParser
import System.Environment (getArgs)

main :: IO ()
main = do putStrLn "Welcome to SAWScript!"
          as <- getArgs
          case as of
            [f] -> process f
            _   -> error "Call with one file name"

process :: String -> IO ()
process f = do
    putStrLn $ "Reading " ++ show f ++ ".."
    cts <- readFile f
    let ast = parseSAW (lexSAW cts)
    print ast
