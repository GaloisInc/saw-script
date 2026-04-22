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
import qualified Data.Map                     as Map
import           Data.Map                     (Map)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)
import           Prettyprinter                (Doc)

import qualified Language.Lean.AST            as Lean
import qualified Language.Lean.Pretty         as Lean

import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Functor

import           SAWCoreLean.Monad
import           SAWCoreLean.SpecialTreatment

-- | Read-only state for translating terms.
--
-- Phase 0 keeps only what a structural walk needs: a map from SAWCore
-- 'VarName' to Lean 'Ident' for variables in scope, and a set of
-- reserved or in-use Lean identifiers so fresh names don't collide.
data TranslationReader = TranslationReader
  { _namedEnvironment  :: Map VarName Lean.Ident
  , _unavailableIdents :: Set Lean.Ident
  }

makeLenses ''TranslationReader

-- | Marker state for the translator. Phase 0 carries nothing — later
-- phases will use this to collect auxiliary declarations discovered
-- during a walk (compare 'SAWCoreRocq.Term.TranslationState').
data TranslationState = TranslationState
  deriving Show

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

-- | Translate a SAWCore constant reference (no arguments).
-- 'ModuleIdentifier' names dispatch through the special-treatment
-- table via 'translateIdentWithArgs'; 'ImportedName's fall back to
-- the short name with any user-supplied 'constantRenaming' applied.
translateConstant :: TermTranslationMonad m => Name -> m Lean.Term
translateConstant nm
  | ModuleIdentifier ident <- nameInfo nm = translateIdentWithArgs ident []
  | otherwise = do
      config <- asks translationConfiguration
      let nm_str = Text.unpack (toShortName (nameInfo nm))
      let renamed = maybe nm_str id (lookup nm_str (constantRenaming config))
      pure (Lean.Var (escapeIdent (Lean.Ident renamed)))

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
  [Lean.Ident] -> -- ^ names of local variables already in scope (e.g. the
                  --   name of the definition being translated, to avoid
                  --   shadowing it)
  (forall m. TermTranslationMonad m => m a) ->
  Either TranslationError (a, TranslationState)
runTermTranslationMonad configuration localEnv =
  runTranslationMonad configuration
    (TranslationReader
       { _namedEnvironment  = Map.empty
       , _unavailableIdents = Set.union reservedIdents (Set.fromList localEnv)
       })
    TranslationState

-- | Combine a term-level 'Binder' with a type-level 'PiBinder', taking
-- the name and type from the 'Binder' but the implicit/explicit status
-- from the 'PiBinder'. Mirrors @SAWCoreRocq.Term.combineBinders@.
combineBinders :: Lean.Binder -> Lean.PiBinder -> Lean.Binder
combineBinders (Lean.Binder _ n mty) (Lean.PiBinder impl _ _) =
  Lean.Binder impl n mty

-- | Given a name, a translated body, and a translated type, produce a
-- Lean 'Decl'. If the body is a lambda and the type is a matching pi,
-- lift the lambda binders into the @def@ signature.
mkDefinition :: Lean.Ident -> Lean.Term -> Lean.Term -> Lean.Decl
mkDefinition name (Lean.Lambda bs t) (Lean.Pi bs' tp)
  | length bs' == length bs =
      Lean.Definition name (zipWith combineBinders bs bs') (Just tp) t
mkDefinition name t tp = Lean.Definition name [] (Just tp) t

-- | Translate a SAWCore 'Term' and its type to a Lean @def@.
translateDefDoc ::
  TranslationConfiguration ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann)
translateDefDoc configuration name body tp = do
  (body', _) <- runTermTranslationMonad configuration [name] (translateTerm body)
  (tp', _)   <- runTermTranslationMonad configuration [name] (translateTerm tp)
  pure (Lean.prettyDecl (mkDefinition name body' tp'))
