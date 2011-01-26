module Main where

import System.Environment (getArgs)
import Data.Version(showVersion)
import qualified Data.Map as M

import Paths_JVM_verifier(version)
import SAWScript.MethodAST(JV)
import SAWScript.Parser(parseJVs)

main :: IO ()
main = do jvs <- getArgs
          case jvs of
            [] -> do putStrLn $ "sawScript v" ++ showVersion version ++ ": no input files"
                     putStrLn $ "Usage: sawScript methodSpecFile.."
            _  -> do parseMap <- parseJVs jvs
                     let s     = M.size parseMap
                         specs = show s ++ " method spec" ++ if s > 1 then "s" else ""
                     putStrLn $ "Loaded " ++ specs ++ " successfully."
                     process parseMap

process :: JV -> IO ()
process m = do mapM_ disp $ M.assocs m
  where disp (f, vs) = do putStrLn $ "=== " ++ show f ++ " ==================="
                          mapM_ print vs
