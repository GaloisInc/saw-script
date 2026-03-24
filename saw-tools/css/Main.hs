{-# Language ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}

module Main where

import           System.Environment( getArgs )
import           System.Exit( exitFailure )
import           System.Console.GetOpt
import           System.IO
import qualified Data.ByteString as BS
import           Data.Text ( pack )

import GHC.IO.Encoding (setLocaleEncoding)

import qualified Cryptol.Eval as E
import           Cryptol.Utils.PP
import           Cryptol.Utils.Logger (quietLogger)

import qualified Data.AIG.CompactGraph as AIG
import qualified Data.AIG.Interface as AIG
import qualified Data.AIG.Operations as AIG

import qualified SAWVersion.Version as Version

import qualified CryptolSAWCore.Cryptol as C
import           SAWCore.SharedTerm
import qualified CryptolSAWCore.Prelude as C
import qualified CryptolSAWCore.CryptolEnv as C
import qualified CryptolSAWCore.TypedTerm as TT


import qualified SAWCoreAIG.BitBlast as BBSim

-- CSS has its own version, because it used to be part of the
-- cryptol-saw-core package, which for its entire existence was always
-- at version 0.1. Keep that for now. We'll print the SAW version as
-- well.
css_version :: String
css_version = "0.1"

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
  [ "Cryptol Symbolic Simulator (css) version " ++ css_version
  , "SAW " ++ Version.versionText
  , "Copyright 2014 Galois, Inc.  All rights reserved."
  ]

header :: String
header = "css [options] <input module> <function to simulate>"

main :: IO ()
main = do
  setLocaleEncoding utf8
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

    sc <- mkSharedContext
    C.scLoadPreludeModule sc
    C.scLoadCryptolModule sc

    let ?fileReader = BS.readFile
    cryenv <- C.initCryptolEnv sc
    cryenv' <- C.importCryptolModule sc cryenv (Left inputModule)
                    Nothing C.PublicAndPrivate Nothing
    processSymbol sc cryenv' out name

cssMain css _ | cssMode css == VersionMode = do
    hPutStr stdout version_string

cssMain css _ | cssMode css == HelpMode = do
    hPutStr stdout (usageInfo header options)

cssMain _ _ = do
    hPutStr stdout (usageInfo header options)
    exitFailure


processSymbol :: SharedContext -> C.CryptolEnv -> FilePath -> String -> IO ()
processSymbol sc cryenv fout funcName = do
   tm <- extractCryptol sc cryenv funcName
   writeAIG sc fout tm

writeAIG :: SharedContext -> FilePath -> Term -> IO ()
writeAIG sc f t = do
  BBSim.withBitBlastedTerm AIG.compactProxy sc mempty t $ \be ls -> do
    AIG.writeAiger f (AIG.Network be (AIG.bvToList ls))

extractCryptol :: SharedContext -> C.CryptolEnv -> String -> IO Term
extractCryptol sc cryenv input = do
  let input' = C.InputText {
          C.inpText = pack input,
          C.inpFile = "<command line>",
          C.inpLine = 1,
          C.inpCol = 1
      }

  let ?fileReader = BS.readFile
  tt <- C.parseTypedTerm sc cryenv input'

  schema <- case TT.ttType tt of
      TT.TypedTermSchema s -> pure s
      _ -> do
          hPutStrLn stderr $ "css: Requested symbol was not a value"
          exitFailure

  putStrLn $ "Extracting expression of type " ++ pretty (C.schemaNoUser schema)
  pure $ TT.ttTerm tt
