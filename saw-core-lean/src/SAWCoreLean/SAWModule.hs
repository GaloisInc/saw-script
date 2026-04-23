{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : SAWCoreLean.SAWModule
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Walker that translates an entire SAWCore 'Module' — its datatypes,
definitions, and injected-code snippets — into a list of Lean
declarations. Near-mirror of "SAWCoreRocq.SAWModule"; the only
notable divergence is that we emit 'Lean.InductiveDecl' rather than
Rocq's @Inductive@ and accept @InjectCodeDecl "Lean"@ instead of
@"Rocq"@.
-}

module SAWCoreLean.SAWModule (translateDecl) where

import           Control.Lens                 (view)
import qualified Control.Monad.Except         as Except
import           Control.Monad                (fail)
import           Control.Monad.Reader         (asks)
import           Data.Maybe                   (listToMaybe)
import qualified Data.Set                     as Set
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)
import           Prettyprinter                (Doc, pretty)

import qualified Language.Lean.AST            as Lean
import qualified Language.Lean.Pretty         as Lean
import           SAWCore.Module
import           SAWCore.Name
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor         (propSort)

import qualified SAWCoreLean.Monad            as M
import           SAWCoreLean.SpecialTreatment
import qualified SAWCoreLean.Term             as TermTranslation
import           SAWCoreLean.Monad

-- | Module-level translation monad. The reader layer carries
-- @(Maybe ModuleName, ModuleMap)@; no mutable state at this layer
-- (all state lives in 'TermTranslation.TranslationState', accessed
-- when we lift into the term monad).
type ModuleTranslationMonad m =
  M.TranslationMonad (Maybe ModuleName, ModuleMap) () m

runModuleTranslationMonad ::
  M.TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  (forall m. ModuleTranslationMonad m => m a) ->
  Either M.TranslationError (a, ())
runModuleTranslationMonad configuration modName mm =
  M.runTranslationMonad configuration (modName, mm) ()

-- | Lift a term-translation action into the module monad by running
-- it in a fresh term-translation state. Discards the final state —
-- suitable when the only result you want is the translated value.
liftTermTranslationMonad ::
  (forall n. TermTranslation.TermTranslationMonad n => n a) ->
  (forall m. ModuleTranslationMonad m => m a)
liftTermTranslationMonad n = fst <$> liftTermTranslationMonadState n

-- | Like 'liftTermTranslationMonad' but also returns the final
-- 'TermTranslation.TranslationState' — lets the caller inspect e.g.
-- the 'universeVars' seen during the sub-translation.
liftTermTranslationMonadState ::
  (forall n. TermTranslation.TermTranslationMonad n => n a) ->
  (forall m. ModuleTranslationMonad m =>
   m (a, TermTranslation.TranslationState))
liftTermTranslationMonadState n = do
  configuration <- asks translationConfiguration
  (modname, mm) <- asks otherConfiguration
  case TermTranslation.runTermTranslationMonad configuration modname mm [] [] n of
    Left e            -> Except.throwError e
    Right (a, state)  -> pure (a, state)

-- | Strip the outermost pi binder from a Lean type. Used to remove
-- the inductive parameters that SAWCore carries on each constructor's
-- type but that Lean's @inductive ... where@ shape factors out.
dropPi :: Lean.Term -> Lean.Term
dropPi (Lean.Pi (_ : t) r) = Lean.Pi t r
dropPi (Lean.Pi _       r) = dropPi r
dropPi t                   = t

-- | Translate a single constructor. 'inductiveParameters' is used to
-- trim the leading pi-binders off the constructor's SAWCore type —
-- those parameters are factored out into the 'Inductive' record and
-- must not reappear on each constructor.
translateCtor ::
  ModuleTranslationMonad m =>
  [Lean.Binder] -> -- ^ the inductive's parameter list; only its length matters
  Ctor -> m Lean.Constructor
translateCtor inductiveParameters (Ctor {..}) = do
  maybeConstructorName <-
    case nameInfo ctorName of
      ModuleIdentifier ident ->
        liftTermTranslationMonad (TermTranslation.translateIdentToIdent ident)
      ImportedName{} -> pure Nothing
  let constructorName = case maybeConstructorName of
        Just (Lean.Ident n) ->
          -- Strip leading @Module.TypeName.@ — Lean's inductive
          -- namespace supplies that qualification automatically at
          -- use sites.
          Lean.Ident (reverse (takeWhile (/= '.') (reverse n)))
        Nothing ->
          error "translateCtor: constructor has no UsePreserve/UseRename target"
  constructorType <-
    (\t -> iterate dropPi t !! length inductiveParameters) <$>
      liftTermTranslationMonad (TermTranslation.translateTerm ctorType)
  pure Lean.Constructor
    { Lean.constructorName = constructorName
    , Lean.constructorType = constructorType
    }

-- | Translate a SAWCore 'DataType' to a Lean @inductive@.
translateDataType :: ModuleTranslationMonad m => DataType -> m Lean.Decl
translateDataType (DataType {..}) =
  case nameInfo dtName of
    ModuleIdentifier dtIdent ->
      atDefSite <$> findSpecialTreatment dtIdent >>= \case
        DefPreserve             -> translateNamed (Lean.Ident (identName dtIdent))
        DefRename   targetName  -> translateNamed targetName
        DefReplace  str         -> pure (Lean.Snippet str)
        DefSkip                 -> pure (skipped dtIdent)
    ImportedName{} ->
      translateNamed (Lean.Ident (Text.unpack (toShortName (nameInfo dtName))))
  where
    translateNamed :: ModuleTranslationMonad m => Lean.Ident -> m Lean.Decl
    translateNamed name = do
      let inductiveName = name
      -- Run parameter/index/sort translation + constructor translation
      -- under one term-monad invocation so we can collect every
      -- universe variable that any component references and emit
      -- them all on the inductive's universe-binder list.
      ((inductiveParameters, inductiveIndices), state) <-
        liftTermTranslationMonadState $
          TermTranslation.translateParams dtParams $ \ps ->
          TermTranslation.translateParams dtIndices $ \ixs -> do
            let errorBecause msg =
                  error ("translateDataType.translateNamed: " ++ msg)
                toPiBinder = \case
                  Lean.Binder Lean.Explicit s (Just t) ->
                    Lean.PiBinder Lean.Explicit (Just s) t
                  Lean.Binder Lean.Explicit _ Nothing ->
                    errorBecause "encountered a Binder without a Type"
                  Lean.Binder Lean.Implicit _ _ ->
                    errorBecause "encountered an implicit index binder"
                  Lean.Binder Lean.Instance _ _ ->
                    errorBecause "encountered an instance index binder"
                pis = map toPiBinder ixs
            pure (ps, pis)
      -- 'translateCtor' runs in the module monad, so each constructor
      -- gets its own fresh term state. (Its universeVars aren't
      -- gathered here; constructor types are closed over the params.)
      inductiveConstructors <-
        mapM (translateCtor inductiveParameters) dtCtors
      let inductiveUniverses =
            Set.toAscList (view TermTranslation.universeVars state)
          -- SAWCore's @dtSort@ is the resulting sort. Lean requires
          -- an inductive's result sort to be predicatively above
          -- @Prop@: either @Prop@ exactly, or a form that can't
          -- reduce to @Prop@ (@Type _@ / @Sort (max 1 _)@). For a
          -- universe-polymorphic inductive, emit 'Sort (max 1 u)'
          -- on the first universe variable so the result sort
          -- accommodates the parameters regardless of what sort
          -- level they're instantiated at.
          inductiveSort
            | dtSort == propSort                        = Lean.Prop
            | Just u <- listToMaybe inductiveUniverses  = Lean.SortMax1Var u
            | otherwise                                 = Lean.Type
      pure $ Lean.InductiveDecl $ Lean.Inductive
        { Lean.inductiveUniverses
        , Lean.inductiveName
        , Lean.inductiveParameters
        , Lean.inductiveIndices
        , Lean.inductiveSort
        , Lean.inductiveConstructors
        }

-- | Emit a @/- … was skipped -/@ comment in place of a declaration
-- whose def-site treatment is 'DefSkip'. Mirrors
-- 'SAWCoreRocq.SAWModule.skipped'.
skipped :: Ident -> Lean.Decl
skipped sawIdent =
  Lean.Comment $ show sawIdent ++ " was skipped"

-- | Same as 'skipped' but for a bare 'NameInfo' (used when the
-- skipped definition doesn't have a module-qualified 'Ident').
skipped' :: NameInfo -> Lean.Decl
skipped' nmi =
  Lean.Comment $ show (toAbsoluteName nmi) ++ " was skipped"

-- | Translate a SAWCore 'Def' to a Lean 'Decl'.
translateDef :: ModuleTranslationMonad m => Def -> m Lean.Decl
translateDef (Def {..}) = do
  specialTreatment <- findSpecialTreatment' (nameInfo defName)
  go (atDefSite specialTreatment)
  where
    go :: ModuleTranslationMonad m => DefSiteTreatment -> m Lean.Decl
    go DefPreserve =
      translateNamed (Lean.Ident (Text.unpack (toShortName (nameInfo defName))))
    go (DefRename targetName) = translateNamed targetName
    go (DefReplace str) = pure (Lean.Snippet str)
    go DefSkip = pure (skipped' (nameInfo defName))

    translateNamed :: ModuleTranslationMonad m => Lean.Ident -> m Lean.Decl
    translateNamed name = do
      -- Run the term translation inside the term monad so we can
      -- harvest 'universeVars' (populated by 'translateSort' for
      -- each distinct @sort k@ seen). Emit as a universe-polymorphic
      -- Lean decl: @def foo.{u0 u1} : ty := body@.
      case defQualifier of
        NoQualifier -> case defBody of
          Nothing -> error "translateDef: non-axiom/primitive without a body"
          Just body -> do
            ((ty, bd), state) <-
              liftTermTranslationMonadState $
                (,) <$> TermTranslation.translateTerm defType
                    <*> TermTranslation.translateTerm body
            let univs = Set.toAscList
                          (view TermTranslation.universeVars state)
            -- Emit as 'noncomputable def'. The generated preludes
            -- use @Foo.rec@ freely, and Lean forbids non-noncomputable
            -- defs from invoking auto-generated recursors. Marking
            -- every prelude-walker def noncomputable is a safe
            -- over-approximation — the generated file is for
            -- type-checking, not execution.
            pure (TermTranslation.mkDefinitionWith Lean.Noncomputable
                    univs name bd ty)
        AxiomQualifier -> emitAxiom
        PrimQualifier  -> emitAxiom
      where
        emitAxiom :: ModuleTranslationMonad m => m Lean.Decl
        emitAxiom = do
          (ty, state) <-
            liftTermTranslationMonadState
              (TermTranslation.translateTerm defType)
          let univs = Set.toAscList
                        (view TermTranslation.universeVars state)
          pure (Lean.Axiom univs name ty)

-- | Translate a single 'ModuleDecl' to a Lean 'Doc'. The public
-- entry — 'SAWCoreLean.Lean.translateSAWModule' maps this over the
-- full 'Module' and wraps the result in a namespace.
translateDecl ::
  SharedContext ->
  M.TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  ModuleDecl ->
  IO (Doc ann)
translateDecl sc configuration modname mm decl =
  let go :: (forall m. ModuleTranslationMonad m => m Lean.Decl) ->
            IO (Doc ann)
      go k =
        case runModuleTranslationMonad configuration modname mm k of
          Right (tdecl, _) -> pure (Lean.prettyDecl tdecl)
          Left e -> do
            msg <- ppTranslationError sc e
            fail (Text.unpack msg)
  in
  case decl of
    TypeDecl td -> go (translateDataType td)
    DefDecl  dd -> go (translateDef dd)
    InjectCodeDecl ns txt
      | ns == "Lean" -> pure (pretty txt)
      | otherwise    -> pure mempty
