{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module SAWCoreIsabelle.TranslateSAW 
  ( writeTerm
  , writeCryptolModules
  , execTopTT
  , TopTTEnv(..)
  , TopTT
  ) where

import           Control.Monad (forM)
import           Control.Monad.Except
import           Control.Monad.Reader
import qualified Data.IntMap as IntMap
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           System.FilePath (takeBaseName, takeDirectory)

import qualified SAWCore.Name as SAW
import           SAWCore.SharedTerm (Term)
import qualified SAWCore.SharedTerm as SAW
import qualified SAWSupport.Pretty as PPS
import qualified SAWCore.Term.Functor as SAW
import           SAWCore.Term.Pretty (termVarNames)

import qualified CryptolSAWCore.SAWCoreCryptol as SAW
import qualified CryptolSAWCore.CryptolEnv as SAW

import qualified Language.Isabelle.Name as Isabelle
import qualified Language.Isabelle.Syntax as Isabelle

import           SAWCoreIsabelle.Options
import           SAWCoreIsabelle.Runner

import Cryptol.Parser.AST (Located(..))
import Cryptol.ModuleSystem.Env (LoadedModules(..), ModuleEnv (..))


data TopTTEnv = 
    TopTTEnv { ttSc :: SAW.SharedContext, ttCryEnv :: SAW.CryptolEnv, ttPPOpts :: PPS.Opts }

newtype TopTT a = TopTT { unTopTT :: ExceptT String (ReaderT TopTTEnv IO) a }
  deriving (Applicative, Functor, Monad, MonadError String, MonadReader TopTTEnv, MonadIO)

instance MonadFail TopTT where
  fail msg = throwError msg

runTopTT :: TopTTEnv -> TopTT a -> IO (Either String a)
runTopTT env f = runReaderT (runExceptT (unTopTT f)) env

execTopTT :: TopTTEnv -> TopTT () -> IO (Maybe String)
execTopTT env f = runTopTT env f >>= \case
  Left msg -> return $ Just msg
  Right () -> return Nothing

prettyTerm :: Term -> TopTT PPS.Doc
prettyTerm t = do
  sc <- asks ttSc
  opts <- asks ttPPOpts
  liftIO $ SAW.prettyTerm sc opts t

-- | Lift any free variables into a bound Pi. Has no effect on closed terms.
liftFrees :: Term -> TopTT Term
liftFrees t = do
  sc <- asks ttSc
  let varTypes = SAW.varTypes t
  varNames <- forM (Set.toAscList $ termVarNames t) $ \vn -> 
    case IntMap.lookup (SAW.vnIndex vn) varTypes of
      Just tT -> return (vn, tT)
      Nothing -> do
        doc <- prettyTerm t
        fail $ "Invalid term shape: " ++ show doc
  liftIO $ SAW.scPiList sc varNames t

writeTerm ::
  Text ->
  FilePath ->
  Term ->
  TopTT ()
writeTerm tnm dest t = do
  sc <- asks ttSc
  cenv <- asks ttCryEnv
  opts <- asks ttPPOpts
  t' <- liftFrees t
  let mkterm = case SAW.termSortOrType t' of
        Left SAW.PropSort -> SAW.propToSchemaExpr
        _ -> SAW.termToSchemaExpr
  (liftIO $ mkterm sc cenv t') >>= \case
    Left err -> do
      msg <- liftIO $ SAW.prettyTTError opts err 
      fail (PPS.render opts msg)
    Right (s,e) -> do
      let 
        thynm = takeBaseName dest
        thynm' = Isabelle.TheoryName thynm False
        tnm' = Isabelle.Name thynm' (Text.unpack tnm) Isabelle.NoSyn Isabelle.Term
        sel = TargetExpr tnm' s e
      writeTarget (takeDirectory dest) sel 

writeCryptolModules ::
  [SAW.ExtCryptolModule] ->
  FilePath ->
  TopTT ()
writeCryptolModules inmods dest = do
  mnms <- forM inmods $ \case
    SAW.ECM_LoadedModule m _ -> return $ thing m
    SAW.ECM_CryptolModule{} -> do
      fail $ "Cannot translate SAW internal cryptol module"
  let sel = case inmods of
        [] -> AllModules
        _ -> ModuleNames mnms
  writeTarget dest sel

writeTarget :: FilePath -> TargetSelect -> TopTT ()
writeTarget dest sel = do
  cenv <- asks ttCryEnv
  let
    me = SAW.eModuleEnv cenv
    mods = lmLoadedModules $ meLoadedModules me

    opts = emptyOpts 
        { isaDestDir_ = dest
        , isaImportPrefix_ = CryptolImage
        , verbosity_ = 1
        , targetSelect_ = sel
        , loggerMsg_ = putStrLn
        , loggerErr_ = putStrLn
        }
  liftIO $ processModules opts mods [] [] >>= \case
    True -> return ()
    False -> fail "Translation to Isabelle failed or was incomplete."