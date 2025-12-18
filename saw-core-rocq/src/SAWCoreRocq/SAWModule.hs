{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : SAWCoreRocq.SAWModule
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module SAWCoreRocq.SAWModule where

import qualified Control.Monad.Except         as Except
import           Control.Monad.Reader         (asks)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)
import           Prettyprinter                (Doc, pretty)

import qualified Language.Rocq.AST            as Rocq
import qualified Language.Rocq.Pretty         as Rocq
import           SAWCore.Module
import           SAWCore.Name
import           SAWCore.SharedTerm

import qualified SAWCoreRocq.Monad            as M
import           SAWCoreRocq.SpecialTreatment
import qualified SAWCoreRocq.Term             as TermTranslation
import           SAWCoreRocq.Monad

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

dropPi :: Rocq.Term -> Rocq.Term
dropPi (Rocq.Pi (_ : t) r) = Rocq.Pi t r
dropPi (Rocq.Pi _       r) = dropPi r
dropPi t                   = t

translateCtor ::
  ModuleTranslationMonad m =>
  [Rocq.Binder] -> -- list of parameters to drop from `ctorType`
  Ctor -> m Rocq.Constructor
translateCtor inductiveParameters (Ctor {..}) = do
  maybe_constructorName <-
    case nameInfo ctorName of
      ModuleIdentifier ident -> liftTermTranslationMonad $ TermTranslation.translateIdentToIdent ident
      ImportedName{} -> pure Nothing
  let constructorName = case maybe_constructorName of
        -- Drop qualifiers from constructor name
        Just (Rocq.Ident n) -> Rocq.Ident (reverse (takeWhile (/= '.') (reverse n)))
        Nothing -> error "translateCtor: unexpected translation for constructor"
  constructorType <-
    -- Unfortunately, `ctorType` qualifies the inductive type's name in the
    -- return type.
    -- dropModuleNameWithinCtor <$>
    -- Unfortunately, `ctorType` comes with the inductive parameters universally
    -- quantified.
    (\ t -> iterate dropPi t !! length inductiveParameters) <$>
    (liftTermTranslationMonad (TermTranslation.translateTerm ctorType))
  return $ Rocq.Constructor
    { constructorName
    , constructorType
    }

translateDataType :: ModuleTranslationMonad m => DataType -> m Rocq.Decl
-- translateDataType (DataType {..})
--   | trace ("translateDataType: " ++ show dtName) False = undefined
translateDataType (DataType {..}) =
  case nameInfo dtName of
    ModuleIdentifier dtIdent ->
      atDefSite <$> findSpecialTreatment dtIdent >>= \case
      DefPreserve            -> translateNamed $ Rocq.Ident (identName dtIdent)
      DefRename   targetName -> translateNamed $ targetName
      DefReplace  str        -> return $ Rocq.Snippet str
      DefSkip                -> return $ skipped dtIdent
    ImportedName{} ->
      translateNamed $ Rocq.Ident (Text.unpack (toShortName (nameInfo dtName)))
  where
    translateNamed :: ModuleTranslationMonad m => Rocq.Ident -> m Rocq.Decl
    translateNamed name = do
      let inductiveName = name
      (inductiveParameters, inductiveIndices) <-
        liftTermTranslationMonad $
        TermTranslation.translateParams dtParams $ \ps ->
        TermTranslation.translateParams dtIndices $ \ixs ->
        -- Translating the indices of a data type should never yield Inhabited
        -- constraints, so the result of calling `translateParams dtIndices` above should
        -- only return explicit, not implicit, Binders.  Moreover, `translateParams`
        -- always returns Binders where the second field is `Just t`, where `t` is the type.
        let errorBecause msg = error $ "translateDataType.translateNamed: " ++ msg in
        let bs = map (\case Rocq.Binder Rocq.Explicit s (Just t) ->
                              Rocq.PiBinder Rocq.Explicit (Just s) t
                            Rocq.Binder Rocq.Explicit _ Nothing ->
                              errorBecause "encountered a Binder without a Type"
                            Rocq.Binder Rocq.Implicit _ _ ->
                              errorBecause "encountered an implicit binder")
                     ixs in
        return (ps, bs)
      let inductiveSort = TermTranslation.translateSort dtSort
      inductiveConstructors <- mapM (translateCtor inductiveParameters) dtCtors
      return $ Rocq.InductiveDecl $ Rocq.Inductive
        { inductiveName
        , inductiveParameters
        , inductiveIndices
        , inductiveSort
        , inductiveConstructors
        }

-- translateModuleDecl :: ModuleTranslationMonad m => ModuleDecl -> m Rocq.Decl
-- translateModuleDecl = \case
--   TypeDecl dataType -> translateDataType dataType
--   DefDecl definition -> translateDef definition

_mapped :: Ident -> Ident -> Rocq.Decl
_mapped sawIdent newIdent =
  Rocq.Comment $ show sawIdent ++ " is mapped to " ++ show newIdent

skipped' :: NameInfo -> Rocq.Decl
skipped' nmi =
  Rocq.Comment $ show (toAbsoluteName nmi) ++ " was skipped"

skipped :: Ident -> Rocq.Decl
skipped sawIdent =
  Rocq.Comment $ show sawIdent ++ " was skipped"

translateDef :: ModuleTranslationMonad m => Def -> m Rocq.Decl
translateDef (Def {..}) = {- trace ("translateDef " ++ show defIdent) $ -} do
  specialTreatment <- findSpecialTreatment' (nameInfo defName)
  translateAccordingly (atDefSite specialTreatment)

  where

    translateAccordingly :: ModuleTranslationMonad m => DefSiteTreatment -> m Rocq.Decl
    translateAccordingly  DefPreserve           = translateNamed $ Rocq.Ident (Text.unpack (toShortName (nameInfo defName)))
    translateAccordingly (DefRename targetName) = translateNamed $ targetName
    translateAccordingly (DefReplace  str)      = return $ Rocq.Snippet str
    translateAccordingly  DefSkip               = return $ skipped' (nameInfo defName)

    translateNamed :: ModuleTranslationMonad m => Rocq.Ident -> m Rocq.Decl
    translateNamed name = liftTermTranslationMonad (go defQualifier defBody)

      where

        go :: TermTranslation.TermTranslationMonad m => DefQualifier -> Maybe Term -> m Rocq.Decl
        go NoQualifier    Nothing     = error "Terms should have a body (unless axiom/primitive)"
        go NoQualifier    (Just body) = Rocq.Definition
                                        <$> pure name
                                        <*> pure []
                                        <*> (Just <$> TermTranslation.translateTerm defType)
                                        <*> TermTranslation.translateTerm body
        go AxiomQualifier _           = Rocq.Axiom
                                        <$> pure name
                                        <*> TermTranslation.translateTerm defType
        go PrimQualifier  _           = Rocq.Axiom
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
    Right (a, _) -> return a

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
        Left e           -> error $ show e
        Right (tdecl, _) -> Rocq.prettyDecl tdecl
    DefDecl dd -> do
      case runModuleTranslationMonad configuration modname mm (translateDef dd) of
        Left e           -> error $ show e
        Right (tdecl, _) -> Rocq.prettyDecl tdecl
    InjectCodeDecl ns txt
      | ns == "Rocq" -> pretty txt
      | otherwise    -> mempty
