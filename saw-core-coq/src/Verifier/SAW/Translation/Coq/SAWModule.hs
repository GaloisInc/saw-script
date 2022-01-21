{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Translation.Coq
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Translation.Coq.SAWModule where

import qualified Control.Monad.Except                          as Except
import           Control.Monad.Reader                          hiding (fail)
import           Prelude                                       hiding (fail)
import           Prettyprinter                                 (Doc, pretty)

import qualified Language.Coq.AST                              as Coq
import qualified Language.Coq.Pretty                           as Coq
import           Verifier.SAW.Module
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Term.Functor
import qualified Verifier.SAW.Translation.Coq.Monad            as M
import           Verifier.SAW.Translation.Coq.SpecialTreatment
import qualified Verifier.SAW.Translation.Coq.Term             as TermTranslation
import Verifier.SAW.Translation.Coq.Monad

-- import Debug.Trace

type ModuleTranslationMonad m =
  M.TranslationMonad TermTranslation.TranslationReader () m

runModuleTranslationMonad ::
  M.TranslationConfiguration -> Maybe ModuleName ->
  (forall m. ModuleTranslationMonad m => m a) ->
  Either (M.TranslationError Term) (a, ())
runModuleTranslationMonad configuration modName =
  M.runTranslationMonad configuration (TermTranslation.TranslationReader modName) ()

dropPi :: Coq.Term -> Coq.Term
dropPi (Coq.Pi (_ : t) r) = Coq.Pi t r
dropPi (Coq.Pi _       r) = dropPi r
dropPi t                  = t

translateCtor ::
  ModuleTranslationMonad m =>
  [Coq.Binder] -> -- list of parameters to drop from `ctorType`
  Ctor -> m Coq.Constructor
translateCtor inductiveParameters (Ctor {..}) = do
  maybe_constructorName <-
    liftTermTranslationMonad $ TermTranslation.translateIdentToIdent ctorName
  let constructorName = case maybe_constructorName of
        Just n -> identName n
        Nothing -> error "translateCtor: unexpected translation for constructor"
  constructorType <-
    -- Unfortunately, `ctorType` qualifies the inductive type's name in the
    -- return type.
    -- dropModuleNameWithinCtor <$>
    -- Unfortunately, `ctorType` comes with the inductive parameters universally
    -- quantified.
    (\ t -> iterate dropPi t !! length inductiveParameters) <$>
    (liftTermTranslationMonad (TermTranslation.translateTerm ctorType))
  return $ Coq.Constructor
    { constructorName
    , constructorType
    }

translateDataType :: ModuleTranslationMonad m => DataType -> m Coq.Decl
-- translateDataType (DataType {..})
--   | trace ("translateDataType: " ++ show dtName) False = undefined
translateDataType (DataType {..}) =
  atDefSite <$> findSpecialTreatment dtName >>= \case
  DefPreserve            -> translateNamed $ identName dtName
  DefRename   targetName -> translateNamed $ targetName
  DefReplace  str        -> return $ Coq.Snippet str
  DefSkip                -> return $ skipped dtName
  where
    translateNamed :: ModuleTranslationMonad m => Coq.Ident -> m Coq.Decl
    translateNamed name = do
      let inductiveName = name
      (inductiveParameters, inductiveIndices) <-
        liftTermTranslationMonad $ do
        ps <- TermTranslation.translateParams dtParams
        ixs <- TermTranslation.translateParams dtIndices
        return (ps, map (\(Coq.Binder s (Just t)) -> Coq.PiBinder (Just s) t) ixs)
      let inductiveSort = TermTranslation.translateSort dtSort
      inductiveConstructors <- mapM (translateCtor inductiveParameters) dtCtors
      return $ Coq.InductiveDecl $ Coq.Inductive
        { inductiveName
        , inductiveParameters
        , inductiveIndices
        , inductiveSort
        , inductiveConstructors
        }

-- translateModuleDecl :: ModuleTranslationMonad m => ModuleDecl -> m Coq.Decl
-- translateModuleDecl = \case
--   TypeDecl dataType -> translateDataType dataType
--   DefDecl definition -> translateDef definition

_mapped :: Ident -> Ident -> Coq.Decl
_mapped sawIdent newIdent =
  Coq.Comment $ show sawIdent ++ " is mapped to " ++ show newIdent

skipped :: Ident -> Coq.Decl
skipped sawIdent =
  Coq.Comment $ show sawIdent ++ " was skipped"

translateDef :: ModuleTranslationMonad m => Def -> m Coq.Decl
translateDef (Def {..}) = {- trace ("translateDef " ++ show defIdent) $ -} do
  specialTreatment <- findSpecialTreatment defIdent
  translateAccordingly (atDefSite specialTreatment)

  where

    translateAccordingly :: ModuleTranslationMonad m => DefSiteTreatment -> m Coq.Decl
    translateAccordingly  DefPreserve           = translateNamed $ identName defIdent
    translateAccordingly (DefRename targetName) = translateNamed $ targetName
    translateAccordingly (DefReplace  str)      = return $ Coq.Snippet str
    translateAccordingly  DefSkip               = return $ skipped defIdent

    translateNamed :: ModuleTranslationMonad m => Coq.Ident -> m Coq.Decl
    translateNamed name = liftTermTranslationMonad (go defQualifier defBody)

      where

        go :: TermTranslation.TermTranslationMonad m => DefQualifier -> Maybe Term -> m Coq.Decl
        go NoQualifier    Nothing     = error "Terms should have a body (unless axiom/primitive)"
        go NoQualifier    (Just body) = Coq.Definition
                                        <$> pure name
                                        <*> pure []
                                        <*> (Just <$> TermTranslation.translateTerm defType)
                                        <*> TermTranslation.translateTerm body
        go AxiomQualifier _           = Coq.Axiom
                                        <$> pure name
                                        <*> TermTranslation.translateTerm defType
        go PrimQualifier  _           = Coq.Axiom
                                        <$> pure name
                                        <*> TermTranslation.translateTerm defType

liftTermTranslationMonad ::
  (forall n. TermTranslation.TermTranslationMonad   n => n a) ->
  (forall m. ModuleTranslationMonad m => m a)
liftTermTranslationMonad n = do
  configuration <- asks translationConfiguration
  configReader <- asks otherConfiguration
  let r = TermTranslation.runTermTranslationMonad configuration configReader [] [] n
  case r of
    Left  e      -> Except.throwError e
    Right (a, _) -> do
      return a

translateDecl ::
  M.TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleDecl ->
  Doc ann
translateDecl configuration modname decl =
  case decl of
  TypeDecl td -> do
    case runModuleTranslationMonad configuration modname (translateDataType td) of
      Left e -> error $ show e
      Right (tdecl, _) -> Coq.ppDecl tdecl
  DefDecl dd -> do
    case runModuleTranslationMonad configuration modname (translateDef dd) of
      Left e -> error $ show e
      Right (tdecl, _) -> Coq.ppDecl tdecl
  InjectCodeDecl ns txt
    | ns == "Coq" -> pretty txt
    | otherwise   -> mempty
