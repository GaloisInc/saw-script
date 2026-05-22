{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Main where

import           Prelude hiding (log)
import           Control.Applicative ((<|>))
import qualified Data.List as List
import           Data.Version ( showVersion )
import qualified Options.Applicative as OA

import           System.Directory (getHomeDirectory, makeAbsolute, getCurrentDirectory)
import           System.Environment (getArgs, lookupEnv)
import           System.Exit (exitFailure, exitSuccess)
import           System.FilePath (splitSearchPath, joinPath, splitDirectories)
import           System.IO (hPutStrLn, stderr)

import qualified Cryptol.Version as Cry

import qualified SAWCoreIsabelle.Options as Options
import           SAWCoreIsabelle.Options 
  (Options(..), ImportPrefix(..), TargetSelect(..))
import qualified SAWCoreIsabelle.Runner as Runner
import           SAWCoreIsabelle.Headless (runTranslator)

import           Paths_saw ( version )

main :: IO ()
main = do
  opts <- parseOptions
  let opts' = Options.addLogger putStrLn $ Options.addErrLogger (hPutStrLn stderr) $ opts
  (runTranslator opts') >>= \case
    True -> exitSuccess
    False -> exitFailure

parseOptions :: IO Options.Options
parseOptions = do
  args <- getArgs
  curDir <- getCurrentDirectory
  let result = OA.execParserPure OA.defaultPrefs (parseInfoOptions curDir Runner.cryptolTheoryHash) args
  case OA.getParseResult result of
    Just opts -> postProcess opts
    Nothing -> OA.handleParseResult result

postProcess :: Options -> IO Options
postProcess opts = do
  srcs <- mapM resolvePath (crySources_ opts)
  dest <- resolvePath $ isaDestDir_ opts
  cryDirsEnv <- maybe [] splitSearchPath <$> lookupEnv cryptolPathEnv
  cryDirs <- mapM resolvePath (cryDirsEnv ++ cryptolDirs_ opts)
  return $ opts { crySources_ = srcs, isaDestDir_ = dest, cryptolDirs_ = cryDirs }

initIsabelleInfo :: String
initIsabelleInfo = List.intercalate ";\n" $ [
    "isabelle components -x $(isabelle components -l | grep \"cryptol\\|cryptl\")"
  , "isabelle components -u saw-core-isabelle/isabelle"
  , "isabelle build -bv Cryptol"
  ]

parseInfoOptions :: FilePath -> String -> OA.ParserInfo Options.Options
parseInfoOptions curDir thyHash =  OA.info (fullVersion <*> shortVersion <*> initIsabelle <*> cryThyInfo <*> OA.helper <*> parser)
  (  OA.fullDesc
  <> OA.progDesc "Generate an Isabelle theory from Cryptol source"
  ) where
  shortVersion = OA.infoOption (showVersion version) $ (OA.long "version" <> OA.help "Show version")
  initIsabelle = OA.infoOption initIsabelleInfo $ (OA.long "init-isabelle" <> OA.help "Print Isabelle setup commands")
  cryThyInfo = OA.infoOption thyHash $ (OA.long "theory-hash" <> OA.help "Print SHA1 hash of Cryptol theories")
  fullVersion = OA.infoOption fullVersionString $ (OA.long "full-version" <> OA.help "Show full version information")
  parser = pure Options.Options
    <*> (OA.many ((OA.strOption
    (  OA.long "source"
    <> OA.short 's'
    <> OA.metavar "<FILE>.cry"
    <> OA.help "Path to cryptol source file"
    )) <|> OA.strArgument OA.idm))
    <*> 
      (OA.strOption
        ( OA.long "dest"
       <> OA.short 'd'
       <> OA.metavar "DIR"
       <> OA.help "Path to output directory"
       <> OA.value curDir
      ))
    <*> parseImport
    <*> (OA.option OA.auto 
     ( OA.long "verbosity" <> OA.value 1 <> OA.metavar "INT" <> OA.help "Logging output verbosity. (0=quiet, 1=info, 2=verbose, 3=debug)" ))
    <*> (OA.switch (OA.long "keep-going" <> OA.help "Attempt to continue translation after errors are raised"))
    <*> (OA.many (OA.strOption 
           ( OA.long "cryptol-path" 
          <> OA.metavar "DIR" 
          <> OA.help "Additional paths to search for cryptol modules"
        )))
    <*> parseModuleSelect
    <*> OA.many (OA.strOption (OA.long "stub" <> OA.help "Only translate the signature of the function with the given qualified name."))
    <*> (pure (\_ -> return ()))
    <*> (pure (\_ -> return ()))

parseImport :: OA.Parser ImportPrefix
parseImport =
      (CustomPrefix <$> OA.strOption (OA.long "prefix" <> OA.short 'p' <> OA.metavar "STR" <> OA.help "Prefix imports with custom string"))
  <|> OA.flag' NoPrefix (OA.long "no-prefix" <> OA.help "Don't add prefix to imports")
  <|> OA.flag CryptolImage CryptolImage (OA.long "cryptol-prefix" <> OA.help "Use 'Cryptol' image qualifier (default)")

parseModuleSelect :: OA.Parser TargetSelect
parseModuleSelect =
      (OA.flag' AllModules (OA.long "all-modules" <> OA.help "Translate all in-scope modules"))
  <|> (NamedModules <$> (OA.some (OA.strOption (OA.long "module" <> OA.help "Name of module to translate"))))
  -- <|> OA.flag TopModule TopModule (OA.long "top-module" <> OA.help "Translate only the toplevel module (default)")


-- | Add special treatment for tilde
resolvePath :: FilePath -> IO FilePath
resolvePath path = do
  path' <- joinPath <$> mapM expandHome (splitDirectories path)
  makeAbsolute path'
  where
    expandHome :: String -> IO String
    expandHome = \case
      "~" -> getHomeDirectory
      s -> return s

cryptolPathEnv :: String
cryptolPathEnv = "CRYPTOLPATH"

fullVersionString :: String
fullVersionString = List.intercalate "\n" $
  [ "cryptol-to-isabelle version: " ++ (showVersion version)
  , "cryptol version: "  ++ (showVersion Cry.version)
  ]