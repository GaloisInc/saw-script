{-# LANGUAGE RankNTypes #-}

module Main where

import           System.Environment( getArgs )
import           System.Exit( exitFailure )
import           System.Console.GetOpt
import           System.IO
import qualified Data.ByteString as BS
import           Data.Text ( pack )
import           Data.Version

import qualified Cryptol.Eval as E
import qualified Cryptol.TypeCheck.AST as T
import qualified Cryptol.ModuleSystem as CM
import qualified Cryptol.ModuleSystem.Env as CME
import qualified Cryptol.Parser as P
import qualified Cryptol.TypeCheck.Solver.SMT as SMT
import           Cryptol.Utils.PP
import           Cryptol.Utils.Logger (quietLogger)

import qualified Data.AIG.CompactGraph as AIG
import qualified Data.AIG.Interface as AIG
import qualified Data.AIG.Operations as AIG

import qualified Verifier.SAW.Cryptol as C
import           Verifier.SAW.SharedTerm
import qualified Verifier.SAW.Cryptol.Prelude as C
import           Verifier.SAW.CryptolEnv (schemaNoUser, meSolverConfig)


import qualified Verifier.SAW.Simulator.BitBlast as BBSim

import qualified Paths_cryptol_saw_core as Paths

data CSS = CSS
  { output :: FilePath
  , cssMode :: CmdMode
  } deriving (Show)

data CmdMode
  = NormalMode
  | HelpMode
  | VersionMode
 deriving (Show, Eq)

emptyCSS :: CSS
emptyCSS =
  CSS
  { output = ""
  , cssMode = NormalMode
  }

options :: [OptDescr (CSS -> CSS)]
options =
  [ Option ['o'] ["output"]
     (ReqArg (\x css -> css{ output = x }) "FILE")
     "output file"
  , Option ['h'] ["help"]
     (NoArg (\css -> css{ cssMode = HelpMode }))
     "display help"
  , Option ['v'] ["version"]
     (NoArg (\css -> css{ cssMode = VersionMode }))
     "version"
  ]

version_string :: String
version_string = unlines
  [ "Cryptol Symbolic Simulator (css) version "++showVersion Paths.version
  , "Copyright 2014 Galois, Inc.  All rights reserved."
  ]

header :: String
header = "css [options] <input module> <function to simulate>"

main :: IO ()
main = do
  args <- getArgs
  case getOpt RequireOrder options args of
    (flags,optArgs,[]) -> cssMain (foldr ($) emptyCSS flags) optArgs

    (_,_,errs) -> do
       hPutStr stderr (concat errs ++ usageInfo header options)
       exitFailure

defaultEvalOpts :: E.EvalOpts
defaultEvalOpts = E.EvalOpts quietLogger E.defaultPPOpts

cssMain :: CSS -> [String] -> IO ()
cssMain css [inputModule,name] | cssMode css == NormalMode = do
    let out = if null (output css)
                 then name++".aig"
                 else (output css)

    modEnv <- CM.initialModuleEnv
    let minp = CM.ModuleInput True (pure defaultEvalOpts) BS.readFile modEnv
    (e,warn) <-
      SMT.withSolver (meSolverConfig modEnv) $ \s ->
      CM.loadModuleByPath inputModule (minp s)
    mapM_ (print . pp) warn
    case e of
       Left msg -> print msg >> exitFailure
       Right (_,menv) -> processModule menv out name

cssMain css _ | cssMode css == VersionMode = do
    hPutStr stdout version_string

cssMain css _ | cssMode css == HelpMode = do
    hPutStr stdout (usageInfo header options)

cssMain _ _ = do
    hPutStr stdout (usageInfo header options)
    exitFailure


processModule :: CM.ModuleEnv -> FilePath -> String -> IO ()
processModule menv fout funcName = do
   sc <- mkSharedContext
   C.scLoadPreludeModule sc
   C.scLoadCryptolModule sc
   tm <- extractCryptol sc menv funcName
   writeAIG sc fout tm

writeAIG :: SharedContext -> FilePath -> Term -> IO ()
writeAIG sc f t = do
  BBSim.withBitBlastedTerm AIG.compactProxy sc mempty t $ \be ls -> do
  AIG.writeAiger f (AIG.Network be (AIG.bvToList ls))

extractCryptol :: SharedContext -> CM.ModuleEnv -> String -> IO Term
extractCryptol sc modEnv input = do
  let declGroups = concatMap T.mDecls (CME.loadedModules modEnv)
  env <- C.importDeclGroups sc C.emptyEnv declGroups
  pexpr <-
    case P.parseExpr (pack input) of
      Left err -> fail (show (P.ppError err))
      Right x -> return x
  let minp = CM.ModuleInput True (pure defaultEvalOpts) BS.readFile modEnv
  (exprResult, exprWarnings) <-
    SMT.withSolver (meSolverConfig modEnv) $ \s ->
    CM.checkExpr pexpr (minp s)
  mapM_ (print . pp) exprWarnings
  ((_, expr, schema), _modEnv') <-
    case exprResult of
      Left err -> fail (show (pp err))
      Right x -> return x
  putStrLn $ "Extracting expression of type " ++ show (pp (schemaNoUser schema))
  C.importExpr sc env expr

