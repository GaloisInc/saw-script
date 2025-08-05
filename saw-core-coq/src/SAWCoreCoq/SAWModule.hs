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
Module      : SAWCoreCoq.SAWModule
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module SAWCoreCoq.SAWModule where

import qualified Control.Monad.Except                          as Except
import           Control.Monad.Reader                          (asks)
import qualified Data.Text                                     as Text
import           Prelude                                       hiding (fail)
import           Prettyprinter                                 (Doc, pretty)

import qualified Language.Coq.AST                              as Coq
import qualified Language.Coq.Pretty                           as Coq
import           SAWCore.Module
import           SAWCore.Name
import           SAWCore.SharedTerm

import qualified SAWCoreCoq.Monad            as M
import           SAWCoreCoq.SpecialTreatment
import qualified SAWCoreCoq.Term             as TermTranslation
import SAWCoreCoq.Monad

-- import Debug.Trace

type ModuleTranslationMonad m =
  M.TranslationMonad (Maybe ModuleName, ModuleMap) () m

runModuleTranslationMonad ::
  M.TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  (forall m. ModuleTranslationMonad m => m a) ->
  Either (M.TranslationError Term) (a, ())
runModuleTranslationMonad configuration modName mm =
  M.runTranslationMonad configuration (modName, mm) ()

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
    case ctorNameInfo of
      ModuleIdentifier ident -> liftTermTranslationMonad $ TermTranslation.translateIdentToIdent ident
      ImportedName{} -> pure Nothing
  let constructorName = case maybe_constructorName of
        -- Drop qualifiers from constructor name
        Just (Coq.Ident n) -> Coq.Ident (reverse (takeWhile (/= '.') (reverse n)))
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
  case dtNameInfo of
    ModuleIdentifier dtIdent ->
      atDefSite <$> findSpecialTreatment dtIdent >>= \case
      DefPreserve            -> translateNamed $ Coq.Ident (identName dtIdent)
      DefRename   targetName -> translateNamed $ targetName
      DefReplace  str        -> return $ Coq.Snippet str
      DefSkip                -> return $ skipped dtIdent
    ImportedName{} ->
      translateNamed $ Coq.Ident (Text.unpack (toShortName dtNameInfo))
  where
    translateNamed :: ModuleTranslationMonad m => Coq.Ident -> m Coq.Decl
    translateNamed name = do
      let inductiveName = name
      (inductiveParameters, inductiveIndices) <-
        liftTermTranslationMonad $
        TermTranslation.translateParamsEC dtParams $ \ps ->
        TermTranslation.translateParamsEC dtIndices $ \ixs ->
        -- Translating the indices of a data type should never yield
        -- Inhabited constraints, so the result of calling
        -- `translateParams dtIndices` above should only return Binders and not
        -- any ImplicitBinders. Moreover, `translateParams` always returns
        -- Binders where the second field is `Just t`, where `t` is the type.
        let errorBecause msg = error $ "translateDataType.translateNamed: " ++ msg in
        let bs = map (\case Coq.Binder s (Just t) ->
                              Coq.PiBinder (Just s) t
                            Coq.Binder _ Nothing ->
                              errorBecause "encountered a Binder without a Type"
                            Coq.ImplicitBinder{} ->
                              errorBecause "encountered an implicit binder")
                     ixs in
        return (ps, bs)
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

skipped' :: NameInfo -> Coq.Decl
skipped' nmi =
  Coq.Comment $ show (toAbsoluteName nmi) ++ " was skipped"

skipped :: Ident -> Coq.Decl
skipped sawIdent =
  Coq.Comment $ show sawIdent ++ " was skipped"

translateDef :: ModuleTranslationMonad m => Def -> m Coq.Decl
translateDef (Def {..}) = {- trace ("translateDef " ++ show defIdent) $ -} do
  specialTreatment <- findSpecialTreatment' (nameInfo defName)
  translateAccordingly (atDefSite specialTreatment)

  where

    translateAccordingly :: ModuleTranslationMonad m => DefSiteTreatment -> m Coq.Decl
    translateAccordingly  DefPreserve           = translateNamed $ Coq.Ident (Text.unpack (toShortName (nameInfo defName)))
    translateAccordingly (DefRename targetName) = translateNamed $ targetName
    translateAccordingly (DefReplace  str)      = return $ Coq.Snippet str
    translateAccordingly  DefSkip               = return $ skipped' (nameInfo defName)

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
  (modname, mm) <- asks otherConfiguration
  let r = TermTranslation.runTermTranslationMonad configuration modname mm [] [] n
  case r of
    Left  e      -> Except.throwError e
    Right (a, _) -> do
      return a

translateDecl ::
  M.TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  ModuleDecl ->
  Doc ann
translateDecl configuration modname mm decl =
  case decl of
  TypeDecl td -> do
    case runModuleTranslationMonad configuration modname mm (translateDataType td) of
      Left e -> error $ show e
      Right (tdecl, _) -> Coq.ppDecl tdecl
  DefDecl dd -> do
    case runModuleTranslationMonad configuration modname mm (translateDef dd) of
      Left e -> error $ show e
      Right (tdecl, _) -> Coq.ppDecl tdecl
  InjectCodeDecl ns txt
    | ns == "Coq" -> pretty txt
    | otherwise   -> mempty
