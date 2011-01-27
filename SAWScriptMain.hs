module Main where

import Control.Monad(zipWithM_)
-- import Data.Version(showVersion)
import Data.Graph
import Data.Maybe(listToMaybe)
import qualified Data.Map as M
import System.Environment (getArgs)

-- import Paths_JVM_verifier(version)
import SAWScript.MethodAST(JVPgm(..))
import SAWScript.Parser(parseJVPgm)
import SAWScript.Utils

main :: IO ()
main = do jvs <- getArgs
          case jvs of
            [f] -> do (pgm@(JVPgm _ parseMap), deps) <- parseJVPgm f
                      case checkCycles deps of
                        Just c  -> complainCycle c
                        Nothing -> let cnt   = M.size parseMap
                                       specs = show cnt ++ " SAW sript" ++ if cnt > 1 then "s" else ""
                                   in do putStrLn $ "Loaded " ++ specs ++ " successfully."
                                         process pgm
            _  -> putStrLn $ "Usage: sawScript <methodSpecFile>"

checkCycles :: M.Map FilePath [(FilePath, Pos)] -> Maybe [FilePath]
checkCycles m = listToMaybe [d | CyclicSCC d <- stronglyConnComp g]
  where g = [(f, f, map fst fps) | (f, fps) <- M.assocs m]

complainCycle :: [FilePath] -> IO ()
complainCycle [c] = putStrLn $ "ERROR: SAW script " ++ show c ++ " recursively imports itself."
complainCycle cs  = do putStrLn $ "ERROR: Following SAW scripts specs recursively depend on each other:"
                       mapM_ (putStrLn .  ("        " ++) . show) cs

process :: JVPgm -> IO ()
process (JVPgm _ m) = do putStrLn "*** Starting script dump."
                         zipWithM_ disp [(1::Int)..] (M.assocs m)
                         putStrLn "*** End method-spec dump."
  where disp i (f, vs) = do putStrLn $ "=== " ++ show i ++ ". " ++ show f ++ " ==================="
                            mapM_ print vs
