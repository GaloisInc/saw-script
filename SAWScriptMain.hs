module Main where

import Control.Monad(zipWithM_)
-- import Data.Version(showVersion)
import Data.Graph
import Data.List(sortBy)
import Data.Maybe(listToMaybe)
import Data.Ord(comparing)
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
                        Just c  -> complainCycle deps c
                        Nothing -> let cnt   = M.size parseMap
                                       specs = show cnt ++ " SAW sript" ++ if cnt > 1 then "s" else ""
                                   in do putStrLn $ "Loaded " ++ specs ++ " successfully."
                                         process pgm
            _  -> putStrLn $ "Usage: sawScript <methodSpecFile>"

checkCycles :: M.Map FilePath [(FilePath, Pos)] -> Maybe [FilePath]
checkCycles m = listToMaybe $ sortBy (comparing length) [ns | CyclicSCC ns <- stronglyConnComp g]
  where g = [(f, f, map fst fps) | (f, fps) <- M.assocs m]

complainCycle :: M.Map FilePath [(FilePath, Pos)] -> [FilePath] -> IO ()
complainCycle deps c = do putStrLn $ "ERROR: Mutually recursive SAW script" ++ (if length deps' > 1 then "s" else "") ++ " detected:"
                          mapM_ disp deps'
  where deps' = concat [[ip | ip@(i, _) <- is, i `elem` c] | (f, is) <- M.assocs deps, f `elem` c]
        disp (f, p) = putStrLn $ "  Script: " ++ show f ++ " imported at " ++ show p

process :: JVPgm -> IO ()
process (JVPgm _ m) = do putStrLn "*** Starting script dump."
                         zipWithM_ disp [(1::Int)..] (M.assocs m)
                         putStrLn "*** End method-spec dump."
  where disp i (f, vs) = do putStrLn $ "=== " ++ show i ++ ". " ++ show f ++ " ==================="
                            mapM_ print vs
