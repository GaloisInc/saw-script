{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : SAWCoreLean.Term
Copyright   : Galois, Inc. 2026
License     : BSD3
Maintainer  : saw@galois.com
Stability   : experimental
Portability : portable

Minimal SAWCore 'Term' to "Language.Lean.AST" translator.

Phase 0 scope: handles 'Sort', 'Pi', 'Lambda', 'App', 'Variable', and
'Constant' (via short-name lookup). All other term forms raise
'NotSupported'. No SpecialTreatment table, no shared-subterm lifting,
no module-walk support yet — those arrive in later phases alongside
'SAWCoreLean.CryptolModule' / 'SAWCoreLean.SAWModule'.
-}

module SAWCoreLean.Term
  ( TermTranslationMonad
  , runTermTranslationMonad
  , translateTerm
  , translateDefDoc
  , translateSort
  ) where

import           Control.Lens                 (makeLenses, over, view)
import qualified Control.Monad.Except         as Except
import           Control.Monad.Reader         (MonadReader(local), asks)
import           Control.Monad.State          (MonadState(get), modify)
import qualified Data.Map                     as Map
import           Data.Map                     (Map)
import           Data.Maybe                   (fromMaybe)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)
import           Prettyprinter                (Doc, hardline, vcat)

import qualified Language.Lean.AST            as Lean
import qualified Language.Lean.Pretty         as Lean

import           SAWCore.Module               (Def(..), ModuleMap, ResolvedName(..),
                                               requireNameInMap, resolvedNameType)
import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor

import           SAWCoreLean.Monad
import           SAWCoreLean.SpecialTreatment

-- | Read-only state for translating terms.
data TranslationReader = TranslationReader
  { _namedEnvironment  :: Map VarName Lean.Ident
    -- ^ SAWCore variable names in scope, paired with the Lean identifier
    -- they translate to.
  , _unavailableIdents :: Set Lean.Ident
    -- ^ Lean identifiers already reserved or in use. Used to pick fresh
    -- names that don't shadow.
  , _sawModuleMap      :: ModuleMap
    -- ^ The environment of SAWCore global definitions, used to resolve
    -- 'Constant' references to their bodies for inline translation.
  }

makeLenses ''TranslationReader

-- | Mutable state collected during translation.
data TranslationState = TranslationState
  { _globalDeclarations   :: [Lean.Ident]
    -- ^ Lean names for SAWCore constants we should /not/ re-emit
    -- (either already translated or explicitly skipped by the caller).
  , _topLevelDeclarations :: [Lean.Decl]
    -- ^ Auxiliary Lean declarations discovered while translating a
    -- term — the bodies of the SAWCore constants it references.
    -- Stored most-recently-added first, reversed on output.
  }

makeLenses ''TranslationState

type TermTranslationMonad m =
  TranslationMonad TranslationReader TranslationState m

askTR :: TermTranslationMonad m => m TranslationReader
askTR = asks otherConfiguration

localTR :: TermTranslationMonad m =>
           (TranslationReader -> TranslationReader) -> m a -> m a
localTR f =
  local (\r -> r { otherConfiguration = f (otherConfiguration r) })

-- | A subset of Lean 4's reserved identifiers. Not exhaustive — the
-- Lean parser has more — but covers the ones most likely to collide
-- with names generated from SAWCore.
reservedIdents :: Set Lean.Ident
reservedIdents =
  Set.fromList $ map Lean.Ident $ concatMap words
    [ "_ axiom def example fun if then else let rec match with"
    , "namespace end section open import variable instance theorem"
    , "Prop Type Sort by do return"
    ]

translateSort :: Sort -> Lean.Sort
translateSort s = if s == propSort then Lean.Prop else Lean.Type

-- | Append @'@ until the identifier is not in use.
nextVariant :: Lean.Ident -> Lean.Ident
nextVariant (Lean.Ident s) = Lean.Ident (s ++ "'")

freshVariant :: TermTranslationMonad m => Lean.Ident -> m Lean.Ident
freshVariant x = do
  used <- view unavailableIdents <$> askTR
  let findVariant i = if Set.member i used then findVariant (nextVariant i) else i
  pure (findVariant x)

withUsedLeanIdent :: TermTranslationMonad m => Lean.Ident -> m a -> m a
withUsedLeanIdent ident =
  localTR (over unavailableIdents (Set.insert ident))

-- | SAWCore local name to a safe, fresh Lean identifier.
translateLocalIdent :: TermTranslationMonad m => LocalName -> m Lean.Ident
translateLocalIdent x = freshVariant (Lean.Ident (Text.unpack x))

withSAWVar :: TermTranslationMonad m => VarName -> (Lean.Ident -> m a) -> m a
withSAWVar n f = do
  n_lean <- translateLocalIdent (vnName n)
  withUsedLeanIdent n_lean $
    localTR (over namedEnvironment (Map.insert n n_lean)) $
      f n_lean

-- | Translate a single SAW-core binder: produce a Lean 'Binder' (for
-- lambdas / lets) carrying the type, and extend the environment while
-- running the continuation.
translateBinder :: TermTranslationMonad m => VarName -> Term ->
                   (Lean.Binder -> m a) -> m a
translateBinder vn ty f = do
  ty' <- translateTerm ty
  withSAWVar vn $ \n' ->
    f (Lean.Binder Lean.Explicit n' (Just ty'))

-- | Translate a single SAW-core pi binder: the binder may be anonymous
-- when its identifier does not appear free in the body (detected via
-- SAWCore's convention of naming such binders @\"_\"@).
translatePiBinder :: TermTranslationMonad m => VarName -> Term ->
                     (Lean.PiBinder -> m a) -> m a
translatePiBinder vn ty f = do
  ty' <- translateTerm ty
  let anonymous = vnName vn == "_"
  if anonymous
    then f (Lean.PiBinder Lean.Explicit Nothing ty')
    else withSAWVar vn $ \n' ->
           f (Lean.PiBinder Lean.Explicit (Just n') ty')

translateBinders :: TermTranslationMonad m => [(VarName, Term)] ->
                    ([Lean.Binder] -> m a) -> m a
translateBinders [] f = f []
translateBinders ((n, ty) : rest) f =
  translateBinder n ty $ \b ->
    translateBinders rest $ \bs ->
      f (b : bs)

translatePiBinders :: TermTranslationMonad m => [(VarName, Term)] ->
                      ([Lean.PiBinder] -> m a) -> m a
translatePiBinders [] f = f []
translatePiBinders ((n, ty) : rest) f =
  translatePiBinder n ty $ \b ->
    translatePiBinders rest $ \bs ->
      f (b : bs)

-- | Print a qualified Lean identifier from a SAWCore 'ModuleName' plus
-- a base identifier — @Some.Module.name@.
qualify :: ModuleName -> Lean.Ident -> Lean.Ident
qualify m (Lean.Ident base) =
  Lean.Ident (Text.unpack (Text.intercalate "." (moduleNamePieces m)) ++ "." ++ base)

-- | Apply a 'UseSiteTreatment' to a SAWCore 'Ident' with a list of
-- arguments — the Lean analogue of @applySpecialTreatment@ in
-- "SAWCoreRocq.Term".
translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Lean.Term
translateIdentWithArgs i args = do
  specialTreatment <- findSpecialTreatment i
  apply (atUseSite specialTreatment)
  where
    baseIdent = escapeIdent (Lean.Ident (identName i))
    qualifiedIdent = qualify (translateModuleName (identModule i)) baseIdent

    -- Wrap only when there are actual arguments; otherwise return the
    -- head bare. This keeps translated zero-arity constants as their
    -- natural form (e.g. @NatLit 1@ rather than @App (NatLit 1) []@),
    -- which lets 'UseMacro' entries pattern-match on literals through
    -- nested applications.
    applied :: TermTranslationMonad m => Lean.Term -> [Term] -> m Lean.Term
    applied f [] = pure f
    applied f args' = Lean.App f <$> mapM translateTerm args'

    apply :: TermTranslationMonad m => UseSiteTreatment -> m Lean.Term
    apply UsePreserve = applied (Lean.Var qualifiedIdent) args
    apply (UseRename mTargetMod targetName expl) =
      let qualifiedName = maybe targetName (`qualify` targetName) mTargetMod
          head_ = (if expl then Lean.ExplVar else Lean.Var) qualifiedName
      in
      applied head_ args
    apply (UseMacro n macroFun)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          f <- macroFun <$> mapM translateTerm mArgs
          applied f rest
      | otherwise =
          -- Under-applied macro — the table entry promises to consume n
          -- arguments but fewer were supplied. Surface it explicitly;
          -- emitting a partial application would produce garbage.
          Except.throwError (UnderAppliedMacro (Text.pack (identName i)) n)

-- | Translate a SAWCore constant reference.
--
-- 'ModuleIdentifier' names dispatch through the special-treatment
-- table via 'translateIdentWithArgs' — that path covers every
-- Prelude- and Cryptol-sourced primitive.
--
-- 'ImportedName' names (e.g. Cryptol user-defined functions pulled
-- into SAWCore) aren't in any Prelude table, so we translate their
-- bodies on demand and append them to 'topLevelDeclarations' so the
-- reference at the use site resolves. Mirrors the Rocq translator's
-- 'translateConstant'.
translateConstant :: TermTranslationMonad m => Name -> m Lean.Term
translateConstant nm
  | ModuleIdentifier ident <- nameInfo nm = translateIdentWithArgs ident []
  | otherwise = do
      config <- asks translationConfiguration
      let nm_str = Text.unpack (toShortName (nameInfo nm))
      let renamed = escapeIdent $ Lean.Ident $
                      fromMaybe nm_str (lookup nm_str (constantRenaming config))

      -- Decide whether to emit a definition for this constant.
      alreadySeen <- getNamesOfAllDeclarations
      let skipDef = elem renamed alreadySeen
                 || elem nm_str (constantSkips config)

      mm <- view sawModuleMap <$> askTR
      let resolved  = requireNameInMap nm mm
          maybeBody = case resolved of
            ResolvedDef d -> defBody d
            _             -> Nothing

      case maybeBody of
        _ | skipDef -> pure ()
        Just body -> do
          b  <- withTopTranslationState (translateTerm body)
          tp <- withTopTranslationState (translateTerm (resolvedNameType resolved))
          modify (over topLevelDeclarations (mkDefinition renamed b tp :))
        Nothing -> do
          -- No body (axiom / primitive): emit as a Lean axiom so the
          -- reference still type-checks (caller is responsible for
          -- a realisation, or for skipping it via constantSkips).
          tp <- withTopTranslationState (translateTerm (resolvedNameType resolved))
          modify (over topLevelDeclarations (Lean.Axiom renamed tp :))

      pure (Lean.Var renamed)

-- | Every Lean identifier the translator has already committed to —
-- both user-declared globals and the auxiliary decls we've inlined.
getNamesOfAllDeclarations :: TermTranslationMonad m => m [Lean.Ident]
getNamesOfAllDeclarations = do
  s <- get
  pure (namedDecls (view topLevelDeclarations s) ++ view globalDeclarations s)

-- | The Lean identifiers a list of 'Lean.Decl's declare at the top
-- level (skipping comments, snippets, and section/namespace
-- wrappers' outer name).
namedDecls :: [Lean.Decl] -> [Lean.Ident]
namedDecls = concatMap one
  where
    one (Lean.Axiom n _)                                  = [n]
    one (Lean.Variable n _)                               = [n]
    one (Lean.Definition n _ _ _)                         = [n]
    one (Lean.InductiveDecl (Lean.Inductive n _ _ _ _))   = [n]
    one (Lean.Namespace _ ds)                             = namedDecls ds
    one (Lean.Comment _)                                  = []
    one (Lean.Snippet _)                                  = []

-- | Run a sub-translation in a fresh local scope (empty variable
-- environment, only reserved identifiers unavailable). Used when
-- pulling in a constant's body; the body is closed, so no outer
-- bindings should leak in.
withTopTranslationState :: TermTranslationMonad m => m a -> m a
withTopTranslationState = localTR $ \r ->
  TranslationReader
    { _namedEnvironment  = Map.empty
    , _unavailableIdents = reservedIdents
    , _sawModuleMap      = view sawModuleMap r
    }

-- | Combine a term-level 'Binder' with a type-level 'PiBinder', keeping
-- the binder's identifier and type but the pi's implicit/explicit
-- status. Mirrors @SAWCoreRocq.Term.combineBinders@.
combineBinders :: Lean.Binder -> Lean.PiBinder -> Lean.Binder
combineBinders (Lean.Binder _ n mty) (Lean.PiBinder impl _ _) =
  Lean.Binder impl n mty

-- | Produce a Lean @def@ from a name, translated body, and translated
-- type. If the body is a lambda and the type is a matching pi, the
-- binders are hoisted into the @def@ signature for readability.
mkDefinition :: Lean.Ident -> Lean.Term -> Lean.Term -> Lean.Decl
mkDefinition name (Lean.Lambda bs t) (Lean.Pi bs' tp)
  | length bs' == length bs =
      Lean.Definition name (zipWith combineBinders bs bs') (Just tp) t
mkDefinition name t tp = Lean.Definition name [] (Just tp) t

translateTerm :: TermTranslationMonad m => Term -> m Lean.Term
translateTerm t =
  case unwrapTermF t of

    FTermF ftf -> case ftf of
      Sort s _h -> pure (Lean.Sort (translateSort s))
      _ -> Except.throwError (NotSupported t)

    Pi {} ->
      let (params, body) = asPiList t in
      translatePiBinders params $ \paramTerms -> do
        body' <- translateTerm body
        pure (Lean.Pi paramTerms body')

    Lambda {} ->
      let (params, body) = asLambdaList t in
      translateBinders params $ \paramTerms -> do
        body' <- translateTerm body
        pure (Lean.Lambda paramTerms body')

    App {} ->
      let (f, args) = asApplyAll t in
      case asGlobalDef f of
        Just ident -> translateIdentWithArgs ident args
        Nothing    -> Lean.App <$> translateTerm f <*> traverse translateTerm args

    Constant nm -> translateConstant nm

    Variable nm _tp -> do
      nenv <- view namedEnvironment <$> askTR
      case Map.lookup nm nenv of
        Just ident -> pure (Lean.Var ident)
        Nothing    -> Except.throwError (LocalVarOutOfBounds t)

-- | Run a translation computation in an empty top-level environment.
runTermTranslationMonad ::
  TranslationConfiguration ->
  ModuleMap ->
  [Lean.Ident] -> -- ^ names of local variables already in scope (e.g. the
                  --   name of the definition being translated, to avoid
                  --   shadowing it)
  (forall m. TermTranslationMonad m => m a) ->
  Either TranslationError (a, TranslationState)
runTermTranslationMonad configuration mm localEnv =
  runTranslationMonad configuration
    (TranslationReader
       { _namedEnvironment  = Map.empty
       , _unavailableIdents = Set.union reservedIdents (Set.fromList localEnv)
       , _sawModuleMap      = mm
       })
    (TranslationState
       { _globalDeclarations   = localEnv
       , _topLevelDeclarations = []
       })

-- | Translate a SAWCore 'Term' and its type to a Lean @def@, together
-- with any auxiliary declarations needed to support it (the bodies of
-- constants referenced along the way).
translateDefDoc ::
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann)
translateDefDoc configuration mm name body tp = do
  ((body', tp'), state) <- runTermTranslationMonad configuration mm [name] $
    (,) <$> translateTerm body <*> translateTerm tp
  let auxDecls = reverse (view topLevelDeclarations state)
      mainDecl = mkDefinition name body' tp'
      -- Each 'prettyDecl' already ends with 'hardline'; 'vcat' adds
      -- another between elements, yielding one blank line between
      -- decls.
  pure $ if null auxDecls
    then Lean.prettyDecl mainDecl
    else vcat (map Lean.prettyDecl auxDecls) <> hardline <> Lean.prettyDecl mainDecl
