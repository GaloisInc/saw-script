{-# LANGUAGE CPP #-}
module Main (main) where

import Control.Monad(zipWithM_, when)
import Data.Version(showVersion)
import Data.Graph
import Data.List(sortBy)
import Data.Maybe(listToMaybe)
import Data.Ord(comparing)
import qualified Data.Map as M
import System.Console.CmdArgs
import qualified System.Console.CmdArgs.Explicit as CA(process)
import System.Directory(canonicalizePath, makeRelativeToCurrentDirectory)
import System.Environment (getArgs)
import System.Exit(exitFailure, exitSuccess, exitWith)

import Paths_JVM_verifier(version)
import SAWScript.MethodAST(SSPgm)
import SAWScript.ParserActions(parseSSPgm)
import SAWScript.CommandExec(runProofs)
import SAWScript.Utils

main :: IO ()
main = do ssOpts <- parseArgs
          (pmap, deps) <- parseSSPgm ssOpts
          mbCycle <- checkCycles deps
          case mbCycle of
            Just c  -> do complainCycle deps c
                          exitFailure
            Nothing -> do let cnt   = M.size pmap
                              specs = show cnt ++ " SAW sript" ++ if cnt > 1 then "s" else ""
                          when (verboseAtLeast 2 ssOpts) $ putStrLn $ "Loaded " ++ specs ++ " successfully."
                          if dump ssOpts
                             then do dumpScripts pmap
                                     exitSuccess
                             else do ec <- runProofs ssOpts pmap
                                     exitWith ec

parseArgs :: IO SSOpts
parseArgs = do popts <- getArgs >>= return . CA.process m
               case popts of
                 Left e -> do putStrLn $ "ERROR: Invalid invocation: " ++ e
                              putStrLn $ "Try --help for more information."
                              exitFailure
                 Right c -> do opts <- cmdArgsApply c
                               ep <- canonicalizePath (entryPoint opts)
                               return opts { entryPoint = ep }

 where m = cmdArgsMode $ SSOpts {
              classpath = def &= typ "CLASSPATH"
#ifdef mingw32_HOST_OS
                         &= help "semicolon-delimited list of Java class-path"
#else
                         &= help "colon-delimited list of Java class-path"
#endif
            , jars       = def &= typ "JARS"
#ifdef mingw32_HOST_OS
                         &= help "semicolon-delimited list of jar paths (e.g. --jars=rt.jar;foo.jar)"
#else
                         &= help "colon-delimited list of jar paths (e.g. --jars=jdk1.6/classes.jar:foo.jar)"
#endif
            , verbose    = 1     &= help "Verbosity level, 0 is ultra quiet"
            , dump       = False &= help "Dump files after parsing, and stop"
            , entryPoint = def   &= typFile &= argPos 0
            }
            &= program "sawScript"
            &= summary ("sawScript v" ++ showVersion version ++ ". Copyright 2011 Galois, Inc. All rights reserved.")

canonicalizeDeps :: M.Map FilePath [(FilePath,  Pos)] -> IO (M.Map FilePath [(FilePath, Pos)])
canonicalizeDeps m = mapM mkNode (M.assocs m) >>= return . M.fromList
  where mkNode (f, fps) = do f' <- canonicalizePath f
                             fps' <- mapM (canonicalizePath . fst) fps
                             return (f', zip fps' (map snd fps))

checkCycles :: M.Map FilePath [(FilePath, Pos)] -> IO (Maybe [FilePath])
checkCycles deps = do deps' <- canonicalizeDeps deps
                      let g = [(f, f, map fst fps) | (f, fps) <- M.assocs deps']
                      return $ listToMaybe $ sortBy (comparing length) [ns | CyclicSCC ns <- stronglyConnComp g]

complainCycle :: M.Map FilePath [(FilePath, Pos)] -> [FilePath] -> IO ()
complainCycle deps c = do deps' <- canonicalizeDeps deps
                          let deps'' = reduce deps'
                          putStrLn $ "Cyclic SAW script" ++ (if length deps'' > 1 then "s" else "") ++ " detected:"
                          mapM_ disp deps''
  where reduce ds = concat [[ip | ip@(i, _) <- is, i `elem` c] | (f, is) <- M.assocs ds, f `elem` c]
        disp (f, p) = do p' <- posRelativeToCurrentDirectory p
                         f' <- makeRelativeToCurrentDirectory f
                         putStrLn $ fmtPos p' $ "imports " ++ show f'

dumpScripts :: SSPgm -> IO ()
dumpScripts m = do putStrLn "*** Starting script dump"
                   zipWithM_ disp [(1::Int)..] (M.assocs m)
                   putStrLn "*** End method-spec dump"
  where disp i (f, vs) = do putStrLn $ "=== " ++ show i ++ ". " ++ show f ++ " ==================="
                            mapM_ print vs
