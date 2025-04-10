{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Translation.Coq.Test
Copyright   : Galois, Inc. 2019
License     : BSD3
Maintainer  : val@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Translation.Coq.Test where

import Control.Monad.IO.Class
import Control.Monad.Reader
import qualified Data.Map as Map
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

-- import qualified Language.Coq.Pretty as Coq
-- import Verifier.SAW.CryptolEnv
import Verifier.SAW.Module
import Verifier.SAW.Prelude (preludeModule)
import Verifier.SAW.SharedTerm
import Verifier.SAW.Typechecker
import qualified Verifier.SAW.UntypedAST as Un
import Verifier.SAW.Translation.Coq

configuration :: TranslationConfiguration
configuration = TranslationConfiguration
  { vectorModule   = "SAWCoreVectorsAsCoqVectors"
  }

-- Creating a bunch of terms with no sharing, for testing purposes

natOf :: Integer -> IO Term
natOf i = do
  sc <- mkSharedContext
  scNat sc (fromInteger i)

aVector :: IO Term
aVector = do
  sc   <- mkSharedContext
  typ  <- scNatType sc
  args <- mapM (natOf) [0, 1, 2]
  scVector sc typ args

aRecord :: IO Term
aRecord = do
  sc   <- mkSharedContext
  nat  <- natOf 2
  unit <- scUnitValue sc
  scRecord sc $ Map.fromList [("natField", nat), ("unitField", unit)]

aRecordType :: IO Term
aRecordType = do
  sc       <- mkSharedContext
  natType  <- scNatType  sc
  unitType <- scUnitType sc
  scRecordType sc [("natField", natType), ("unitField", unitType)]

translate :: Monad m => m Term -> m Doc
translate term = do
  translateDeclImports configuration "MyDefinition" <$> term >>= \case
    Left  e -> error $ show e
    Right r -> return r

preludeName :: Un.ModuleName
preludeName = Un.moduleName preludeModule

checkTermVar :: Un.TermVar -> Ident
checkTermVar tv = mkIdent preludeName (Un.termVarString tv) -- FIXME

checkTermCtx :: SCIOMonad m => Un.TermCtx -> m [(Ident, Term)]
checkTermCtx ctx = mapM checkUntypedBinder ctx

checkUntypedBinder :: SCIOMonad m => (Un.TermVar, Un.Term) -> m (Ident, Term)
checkUntypedBinder (ident, term) =
  (,) <$> pure (checkTermVar ident) <*> checkUntypedTerm term

type SCIOMonad m = ( MonadIO m, MonadReader SharedContext m )

checkUntypedTerm :: SCIOMonad m => Un.Term -> m Term
checkUntypedTerm term = do
  sc <- ask
  et <- liftIO $ do
    inferCompleteTerm sc (Just preludeName) term
  case et of
    Left  e -> error $ show e
    Right t -> return t

getPreludeModule :: SCIOMonad m => m Module
getPreludeModule = do
  sc <- ask
  liftIO $ scFindModule sc preludeName

getPreludeDataType :: SCIOMonad m => String -> m DataType
getPreludeDataType name = do
  prelude <- getPreludeModule
  case findDataType prelude name of
    Nothing -> error $ name ++ " not found"
    Just dt -> return dt

translateSAWCorePrelude :: IO ()
translateSAWCorePrelude = do
  sc <- mkSharedContext
  -- In order to get test data types, we load the Prelude
  tcInsertModule sc preludeModule
  flip runReaderT sc $ do

    prelude <- getPreludeModule

    liftIO $ do
      putStrLn "From Coq.Strings  Require Import String."
      putStrLn "From CryptolToCoq Require Import SAWCoreScaffolding."
      putStrLn ""

    doc <- translateModule configuration prelude

    liftIO $ putStrLn $ show doc

-- translateCryptolPrelude :: IO ()
-- translateCryptolPrelude = do
--   sc <- mkSharedContext
--   cryptolEnv <- initCryptolEnv sc
--   forM_ (Map.assocs $ eTermEnv cryptolEnv) $ \ (a, b) -> do
--     putStrLn $ show a
--   return ()

main :: IO ()
main = translateSAWCorePrelude
