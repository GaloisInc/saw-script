{- |
Module           : $Header$
Description      :
Stability        : provisional
Point-of-contact : lerkok
-}

{-# LANGUAGE CPP #-}
module Main (main) where

import Control.Applicative((<$>))
import Control.Monad(zipWithM_)
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
import Text.ParserCombinators.Parsec(runParser, many1, noneOf, sepBy, char)

import Execution.Codebase(Codebase, loadCodebase)

import Paths_jvm_verifier(version)
import SAWScript.MethodAST(SSPgm, VerifierCommand(DeclareMethodSpec))
import SAWScript.ParserActions(parseSSPgm)
import SAWScript.CommandExec(runProofs)
import SAWScript.Utils

main :: IO ()
main = do ssOpts <- parseArgs
          cb <- getCodeBase ssOpts
          (pmap, deps) <- parseSSPgm ssOpts
          mbCycle <- checkCycles deps
          case mbCycle of
            Just c  -> do complainCycle deps c
                          exitFailure
            Nothing -> do let cnt   = M.fold (\a l -> l + noOfSpecs a) 0 pmap
                              plu   = if cnt /= 1 then "s" else ""
                          verboseAtLeast 2 ssOpts $ putStrLn $ "Loaded " ++ show cnt ++ " SAW script" ++ plu ++ " successfully."
                          if dump ssOpts
                             then do dumpScripts pmap
                                     exitSuccess
                             else do notQuiet ssOpts $ putStrLn $ "Starting verification tasks on " ++ show cnt ++ " specification" ++ plu ++ "."
                                     ec <- runProofs cb ssOpts pmap
                                     exitWith ec
  where noOfSpecs :: [VerifierCommand] -> Int
        noOfSpecs cmds = length [() | DeclareMethodSpec{} <- cmds]

parseArgs :: IO SSOpts
parseArgs = do popts <- CA.process m <$> getArgs
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

getCodeBase :: SSOpts -> IO Codebase
getCodeBase opts = loadCodebase jpaths cpaths
  where parse w a emsg = either (const (error emsg)) id (runParser (delimited delimeter) () w a)
        delimited c = many1 (noneOf [c]) `sepBy` char c
        jpaths = parse "jars"      (jars opts)      $ "Unable to parse " ++ msg ++ "-delimited list of jar files"
        cpaths = parse "classpath" (classpath opts) $ "Unable to parse " ++ msg ++ "-delimited CLASSPATH."
#ifdef mingw32_HOST_OS
        delimeter = ';'
        msg       = "semicolon"
#else
        delimeter = ':'
        msg       = "colon"
#endif

canonicalizeDeps :: M.Map FilePath [(FilePath,  Pos)] -> IO (M.Map FilePath [(FilePath, Pos)])
canonicalizeDeps m = M.fromList <$> mapM mkNode (M.assocs m)
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
