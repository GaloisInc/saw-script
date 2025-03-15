{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Main
Copyright   : Galois, Inc. 2019
License     : BSD3
Maintainer  : val@galois.com
Stability   : experimental
Portability : portable
-}

module Main where

import Control.Monad.IO.Class
import Control.Monad.Reader
import qualified Data.Map as Map
import qualified Data.Text as Text
import Prettyprinter

-- import qualified Language.Coq.Pretty as Coq
-- import CryptolSAWCore.CryptolEnv
import SAWCore.Module
import SAWCore.Prelude (preludeModule)
import SAWCore.SharedTerm
import SAWCore.Typechecker
import qualified SAWCore.UntypedAST as Un
import SAWCoreCoq.Coq

configuration :: TranslationConfiguration
configuration = TranslationConfiguration {
    constantRenaming = [],
    constantSkips = [],
    monadicTranslation = False,
    postPreamble = "",
    vectorModule   = "SAWCoreVectorsAsCoqVectors"
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

translate :: Monad m => Term -> Term -> m (Doc ann)
translate term ty = do
  let result = translateTermAsDeclImports configuration "MyDefinition" term ty
  case result of
    Left  e -> error $ show e
    Right r -> return r

preludeName :: Un.ModuleName
preludeName = Un.moduleName preludeModule

checkTermVar :: Un.TermVar -> Ident
checkTermVar tv = mkIdent preludeName (Text.pack $ Un.termVarString tv) -- FIXME

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

getPreludeDataType :: SCIOMonad m => Text.Text -> m DataType
getPreludeDataType name = do
  prelude <- getPreludeModule
  case findDataType prelude name of
    Nothing -> error $ Text.unpack name ++ " not found"
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

    let doc = translateSAWModule configuration prelude

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
