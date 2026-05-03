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
  ( -- * Monad
    TermTranslationMonad
  , TranslationState(..)
  , runTermTranslationMonad
  , globalDeclarations
  , topLevelDeclarations
  , universeVars
    -- * Translation
  , translateTerm
  , translateDefDoc
  , translateSort
  , translateIdentToIdent
  , translateParams
  , translatePiBinders
    -- * Decl construction
  , mkDefinition
  , mkDefinitionWith
  ) where

import           Control.Lens                 (makeLenses, over, view)
import qualified Control.Monad.Except         as Except
import           Control.Monad.Reader         (MonadReader(local), asks)
import           Data.Foldable                (toList)
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

import           SAWCore.Module               (Ctor(..), ModuleMap,
                                               ResolvedName(..),
                                               resolveNameInMap)
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
  , _currentModule     :: Maybe ModuleName
    -- ^ The SAWCore module currently being translated. When a
    -- 'UsePreserve' reference targets this module, emit the short
    -- name unqualified — Lean's namespace scoping already provides
    -- the prefix.
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
  , _universeVars         :: Set String
    -- ^ Universe-variable names seen during translation of the
    -- current declaration. Emitted into the def/axiom's universe
    -- list so the result is well-formed Lean (@def foo.{u0 u1} ...@).
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
    -- @_@ is intentionally *not* reserved: Lean accepts @fun _ => …@
    -- and @(_ : A) -> B@ as valid anonymous-binder syntax. Treating
    -- @_@ as reserved was making the translator rename anonymous
    -- SAWCore binders to @_'@ / @_''@ / @_'''@ (audit finding 2C-3).
    [ "axiom def example fun if then else let rec match with"
    , "namespace end section open import variable instance theorem"
    , "Prop Type Sort by do return"
    ]

-- | Translate a SAWCore 'Sort' into a Lean 'Lean.Sort'.
--
-- Under the specialization architecture (see
-- @doc/2026-04-23_stage3-translator-sketch.md@) every SAWCore term
-- reaching the translator has been fully normalized, so @sort 0@
-- and @sort 1@ positions are all concrete. We emit 'Prop' for
-- 'PropSort' and Lean's @Type = Type 0@ for every 'TypeSort'.
--
-- The earlier P4/P6 universe-polymorphism machinery that allocated
-- a fresh universe variable per @sort k@ occurrence stayed in the
-- AST so the field is still threaded through 'translateDefDoc'; it
-- just collapses to an empty list in this regime.
translateSort :: TermTranslationMonad m => Sort -> m Lean.Sort
translateSort s
  | s == propSort = pure Lean.Prop
  | otherwise     = pure Lean.Type

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

-- | The result of translating a SAWCore binder to Lean: the Lean
-- identifier and the translated type. Pre-specialization we also
-- carried auxiliary @Inhabited@ instance binders here; those are
-- gone (see 'translateBinder'' for rationale).
data BindTrans = BindTrans Lean.Ident Lean.Type

-- | Flatten a 'BindTrans' into a Lean term-level 'Binder' list.
bindTransToBinder :: BindTrans -> [Lean.Binder]
bindTransToBinder (BindTrans name ty) =
  [Lean.Binder Lean.Explicit name (Just ty)]

-- | Flatten a 'BindTrans' into a Lean type-level 'PiBinder' list.
-- Anonymous binders (@_@) collapse to the arrow form.
bindTransToPiBinder :: BindTrans -> [Lean.PiBinder]
bindTransToPiBinder (BindTrans name ty)
  | name == Lean.Ident "_" = [Lean.PiBinder Lean.Explicit Nothing ty]
  | otherwise              = [Lean.PiBinder Lean.Explicit (Just name) ty]

-- | Translate a single SAW-core binder. An earlier revision also
-- injected an @[Inh_a : Inhabited a]@ instance binder for parameters
-- whose SAWCore type carries the @isort@ flag (the "inhabited sort"
-- annotation). We no longer do this: the injected instance binders
-- created positional-argument mismatches when the caller applied a
-- SAWCore term like @Num.rec motive tcnum tcinf n a xs@, where the
-- motive's returned type had an instance binder Lean couldn't insert
-- through the applied chain. SAWCore's @isort@ flag is an advisory
-- about reachability; preserving it as a Lean typeclass binder is
-- not required for soundness of value-level translation.
--
-- If we later need @Inhabited@ reasoning for specific primitives,
-- wire it per-primitive in 'SAWCorePrimitives.lean' rather than
-- sprinkling binders through every parameter list.
translateBinder' :: TermTranslationMonad m => VarName -> Term ->
                    (BindTrans -> m a) -> m a
translateBinder' vn ty f = do
  ty' <- translateTerm ty
  withSAWVar vn $ \n' ->
    f (BindTrans n' ty')

translateBinders' :: TermTranslationMonad m => [(VarName, Term)] ->
                     ([BindTrans] -> m a) -> m a
translateBinders' [] f = f []
translateBinders' ((n, ty) : rest) f =
  translateBinder' n ty $ \bnd ->
    translateBinders' rest $ \bnds ->
      f (bnd : bnds)

-- | Produce a flat list of Lean term-level binders from a SAWCore
-- binding list. Zero-or-more auxiliary 'Inhabited' instance binders
-- may be interleaved (one per binder whose type is an @isort@).
translateBinders :: TermTranslationMonad m => [(VarName, Term)] ->
                    ([Lean.Binder] -> m a) -> m a
translateBinders bs f =
  translateBinders' bs (f . concatMap bindTransToBinder)

-- | Alias for 'translateBinders' under its Rocq-compatible name,
-- used by "SAWCoreLean.SAWModule" when translating data-type
-- parameters.
translateParams :: TermTranslationMonad m => [(VarName, Term)] ->
                   ([Lean.Binder] -> m a) -> m a
translateParams = translateBinders

-- | Produce a flat list of Lean type-level pi binders from a SAWCore
-- binding list. Anonymous binders (@_@) with no auxiliary
-- hypotheses collapse to the @A -> rest@ arrow form.
translatePiBinders :: TermTranslationMonad m => [(VarName, Term)] ->
                      ([Lean.PiBinder] -> m a) -> m a
translatePiBinders bs f =
  translateBinders' bs (f . concatMap bindTransToPiBinder)

-- | Print a qualified Lean identifier from a SAWCore 'ModuleName' plus
-- a base identifier — @Some.Module.name@.
qualify :: ModuleName -> Lean.Ident -> Lean.Ident
qualify m (Lean.Ident base) =
  Lean.Ident (Text.unpack (Text.intercalate "." (moduleNamePieces m)) ++ "." ++ base)

-- | Compute the Lean 'Ident' that a SAWCore 'Ident' resolves to at a
-- use site (before any 'UseRename' / 'UseMacro' treatment). Handles:
--
--   * Data-type constructors: Lean scopes these inside the
--     inductive's namespace (@PairType.PairValue@, not @PairValue@).
--     We detect via 'resolveNameInMap' and prepend the datatype's
--     short name.
--   * Same-module references: Lean's 'namespace' scope supplies the
--     module prefix at use sites, so we emit the short name bare.
--   * Cross-module references: emit fully qualified.
defaultIdentTarget ::
  TermTranslationMonad m => Ident -> m Lean.Ident
defaultIdentTarget i = do
  curMod <- view currentModule <$> askTR
  mm     <- view sawModuleMap <$> askTR
  let short = escapeIdent (Lean.Ident (identName i))
      -- If this ident is a data-type constructor, scope the short
      -- name inside the datatype's short name.
      scopedShort = case resolveNameInMap mm i of
        Just (ResolvedCtor c) ->
          let dtShort = Text.unpack (toShortName (nameInfo (ctorDataType c)))
          in  Lean.Ident (dtShort ++ "." ++ identName i)
        _ -> short
      sameModule = Just (identModule i) == curMod
  pure $
    if sameModule
      then scopedShort
      else qualify (translateModuleName (identModule i)) scopedShort

-- | Resolve a SAWCore 'Ident' to the Lean 'Ident' used at its use
-- sites, when that mapping is fixed (i.e. the treatment is
-- 'UsePreserve' or 'UseRename'). Returns 'Nothing' for 'UseMacro'
-- entries, which don't have a single Lean ident to point at.
-- Mirrors @SAWCoreRocq.Term.translateIdentToIdent@.
translateIdentToIdent :: TermTranslationMonad m => Ident -> m (Maybe Lean.Ident)
translateIdentToIdent i = do
  qualifiedIdent <- defaultIdentTarget i
  treatment      <- atUseSite <$> findSpecialTreatment i
  case treatment of
    UsePreserve -> pure (Just qualifiedIdent)
    UseRename mTargetMod targetName _ ->
      pure $ Just $ case mTargetMod of
        Just mod_
          | isImplicitlyOpened mod_ -> targetName
          | otherwise               -> qualify mod_ targetName
        Nothing                     -> targetName
    UseMacro _ _      -> pure Nothing
    UseMacroOrVar{}   -> pure Nothing
    UseReject reason  ->
      Except.throwError
        (RejectedPrimitive (Text.pack (identName i)) reason)

-- | Apply a 'UseSiteTreatment' to a SAWCore 'Ident' with a list of
-- arguments — the Lean analogue of @applySpecialTreatment@ in
-- "SAWCoreRocq.Term".
translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Lean.Term
translateIdentWithArgs i args = do
  specialTreatment <- findSpecialTreatment i
  qualifiedIdent   <- defaultIdentTarget i
  mm               <- view sawModuleMap <$> askTR
  -- SAWCore applies all arguments (including datatype parameters) to
  -- a constructor explicitly. Lean's auto-generated @MyData.ctor@
  -- takes datatype parameters /implicitly/, so we emit a leading
  -- @\@@ to force all arguments explicit.
  let isCtor = case resolveNameInMap mm i of
        Just (ResolvedCtor _) -> True
        _                     -> False
  apply isCtor qualifiedIdent (atUseSite specialTreatment)
  where
    -- Wrap only when there are actual arguments; otherwise return the
    -- head bare. This keeps translated zero-arity constants as their
    -- natural form (e.g. @NatLit 1@ rather than @App (NatLit 1) []@),
    -- which lets 'UseMacro' entries pattern-match on literals through
    -- nested applications.
    applied :: TermTranslationMonad m => Lean.Term -> [Term] -> m Lean.Term
    applied f [] = pure f
    applied f args' = Lean.App f <$> mapM translateTerm args'

    apply :: TermTranslationMonad m =>
             Bool -> Lean.Ident -> UseSiteTreatment -> m Lean.Term
    apply isCtor qualifiedIdent UsePreserve =
      let head_ = (if isCtor then Lean.ExplVar else Lean.Var) qualifiedIdent
      in applied head_ args
    apply isCtor _ (UseRename mTargetMod targetName expl) = do
      -- Resolving a use-site reference via a 'rename' / 'mapsTo'
      -- entry.
      --
      --   * If the caller explicitly supplied a target module
      --     (@Just mod_@) AND that module is in the implicit-open
      --     list (see 'isImplicitlyOpened'), emit the bare target
      --     name — the preamble's @open@ makes it resolve, and the
      --     output is dramatically shorter.
      --   * Else if the caller supplied a target module, emit
      --     fully-qualified.
      --   * Otherwise, if the target name already contains a '.'
      --     (e.g. @Eq.refl@), it's a pre-qualified Lean name that
      --     the caller wants emitted as-is.
      --   * Otherwise, if the SAWCore ident is a constructor, scope
      --     the new short name inside the datatype's short name
      --     (Lean inductives @C.ctor@).
      mm <- view sawModuleMap <$> askTR
      curMod <- view currentModule <$> askTR
      let Lean.Ident tName = targetName
          alreadyQualified = '.' `elem` tName
          scopedTarget = case mTargetMod of
            Just mod_
              | isImplicitlyOpened mod_ -> targetName
              | otherwise               -> qualify mod_ targetName
            Nothing
              | alreadyQualified -> targetName
              | isCtor, Just (ResolvedCtor c) <- resolveNameInMap mm i ->
                  let dtShort = Text.unpack (toShortName (nameInfo (ctorDataType c)))
                      scopedShort = Lean.Ident (dtShort ++ "." ++ tName)
                      sameModule = Just (identModule i) == curMod
                  in if sameModule
                       then scopedShort
                       else qualify (translateModuleName (identModule i)) scopedShort
              | otherwise -> targetName
          head_ = (if expl then Lean.ExplVar else Lean.Var) scopedTarget
      applied head_ args
    apply _ _ (UseMacro n macroFun)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          f <- macroFun <$> mapM translateTerm mArgs
          applied f rest
      | otherwise =
          -- Under-applied macro — the table entry promises to consume n
          -- arguments but fewer were supplied. Surface it explicitly;
          -- emitting a partial application would produce garbage.
          Except.throwError (UnderAppliedMacro (Text.pack (identName i)) n)
    apply _ _ (UseMacroOrVar n fallback macroFun)
      | length args >= n
      , (mArgs, rest) <- splitAt n args = do
          f <- macroFun <$> mapM translateTerm mArgs
          applied f rest
      | otherwise =
          -- Under-applied: emit the fallback term as the head and
          -- apply whatever args we did receive. Lean will eta-expand
          -- as needed at use sites.
          applied fallback args
    apply _ _ (UseReject reason) =
      Except.throwError
        (RejectedPrimitive (Text.pack (identName i)) reason)

-- | Translate a SAWCore constant reference.
--
-- Under the specialization architecture (see
-- @doc/2026-04-23_stage3-translator-sketch.md@) 'scNormalize' has
-- already unfolded every defined constant before the translator is
-- called, so any 'Constant' reaching this function is one of:
--
--   * a 'ModuleIdentifier' that dispatches through
--     'SpecialTreatment' (axioms, primitives, inductive types and
--     constructors, recursors that survive normalization).
--   * an 'ImportedName' for a Cryptol-user-introduced constant we
--     have no special treatment for. We emit a bare qualified
--     reference; the caller is expected to supply a realisation (or
--     the name resolves to something in the existing Cryptol
--     preamble). Pre-specialization this branch recursively
--     translated the constant's body; that is now dead code because
--     normalization would have unfolded the body in-place.
translateConstant :: TermTranslationMonad m => Name -> m Lean.Term
translateConstant nm
  | ModuleIdentifier ident <- nameInfo nm = translateIdentWithArgs ident []
  | otherwise = do
      config <- asks translationConfiguration
      let nm_str  = Text.unpack (toShortName (nameInfo nm))
      let renamed = escapeIdent $ Lean.Ident $
                      fromMaybe nm_str (lookup nm_str (constantRenaming config))
      pure (Lean.Var renamed)

-- | Combine a term-level 'Binder' with a type-level 'PiBinder', keeping
-- the binder's identifier and type but the pi's implicit/explicit
-- status. Mirrors @SAWCoreRocq.Term.combineBinders@.
combineBinders :: Lean.Binder -> Lean.PiBinder -> Lean.Binder
combineBinders (Lean.Binder _ n mty) (Lean.PiBinder impl _ _) =
  Lean.Binder impl n mty

-- | Produce a Lean @def@ from a name, translated body, and translated
-- type. If the body is a lambda and the type is a matching pi, the
-- binders are hoisted into the @def@ signature for readability.
-- The resulting decl is marked 'Computable'; callers that need
-- 'noncomputable' (e.g. the module-level prelude walker) post-process
-- via 'setNoncomputable'.
--
-- The universe-variable list is populated externally via
-- 'mkDefinitionWith'; 'mkDefinition' defaults to the empty list.
mkDefinition :: Lean.Ident -> Lean.Term -> Lean.Term -> Lean.Decl
mkDefinition = mkDefinitionWith Lean.Computable []

-- | Generalised 'mkDefinition' that lets the caller pick the
-- 'Noncomputable' flag and a list of universe-variable names the
-- body and type may reference. The list is filtered by what the
-- emitted decl actually mentions — the type and body are translated
-- separately and may independently allocate universe variables that
-- get shadowed when Lambda binders hoist into the @def@ signature.
-- Declaring only the referenced ones matches what Lean expects.
--
-- If the body is a 'Lambda' with more binders than the type has
-- 'Pi' binders, or vice versa, the surplus stays in the body /
-- type as-is. Crucially, we strip the /type annotations/ from the
-- body's outer lambdas when the signature already supplies them —
-- otherwise Lean re-elaborates the annotated binder against the
-- signature's binder, and the body-side's universe variables go
-- unused (they're only referenced by the redundant annotation
-- Lean ignores).
mkDefinitionWith ::
  Lean.Noncomputable -> [String] ->
  Lean.Ident -> Lean.Term -> Lean.Term -> Lean.Decl
mkDefinitionWith nc univs name body tp =
  let raw = case (body, tp) of
        (Lean.Lambda bs t, Lean.Pi bs' tp')
          | length bs == length bs' ->
              -- Lengths match: hoist lambda binders into signature.
              Lean.Definition nc [] name (zipWith combineBinders bs bs')
                              (Just tp') t
          | length bs < length bs' ->
              -- Body has fewer lambdas than type has pi binders.
              -- Emit the body alone (the remaining pi binders stay
              -- in the signature's type).
              Lean.Definition nc [] name [] (Just tp)
                              (Lean.Lambda (map stripType bs) t)
        _ -> Lean.Definition nc [] name [] (Just tp) body
      used = usedUniversesInDecl raw
      keep = filter (`Set.member` used) univs
  in rebrandUnivs keep raw
  where
    rebrandUnivs us (Lean.Definition nc' _ nm bs mty bd) =
      Lean.Definition nc' us nm bs mty bd
    rebrandUnivs _ d = d

    -- | Drop the type annotation from a lambda binder. Lean will
    -- infer the type from the surrounding @def@'s pi signature.
    stripType :: Lean.Binder -> Lean.Binder
    stripType (Lean.Binder impl n _) = Lean.Binder impl n Nothing

-- | Collect every universe-variable name mentioned in a 'Lean.Decl'
-- by walking its AST. Used to filter the per-def universe list down
-- to the variables that are actually referenced after 'mkDefinition'
-- hoists binders (the type and the body may have introduced separate
-- shadowed variables).
usedUniversesInDecl :: Lean.Decl -> Set String
usedUniversesInDecl d = case d of
  Lean.Axiom _ _ ty -> usedUniversesInTerm ty
  Lean.Variable _ ty -> usedUniversesInTerm ty
  Lean.Definition _ _ _ bs mty bd ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder bs)
      , maybe Set.empty usedUniversesInTerm mty
      , usedUniversesInTerm bd
      ]
  Lean.InductiveDecl (Lean.Inductive _ _ ps ixs s ctors) ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder ps)
      , Set.unions (map usedUniversesInPiBinder ixs)
      , usedUniversesInSort s
      , Set.unions [ usedUniversesInTerm t | Lean.Constructor _ t <- ctors ]
      ]
  Lean.Namespace _ ds -> Set.unions (map usedUniversesInDecl ds)
  Lean.Comment _ -> Set.empty
  Lean.Snippet _ -> Set.empty

usedUniversesInBinder :: Lean.Binder -> Set String
usedUniversesInBinder (Lean.Binder _ _ mty) =
  maybe Set.empty usedUniversesInTerm mty

usedUniversesInPiBinder :: Lean.PiBinder -> Set String
usedUniversesInPiBinder (Lean.PiBinder _ _ ty) = usedUniversesInTerm ty

usedUniversesInSort :: Lean.Sort -> Set String
usedUniversesInSort = \case
  Lean.Prop            -> Set.empty
  Lean.TypeLvl _       -> Set.empty
  Lean.SortVar u       -> Set.singleton u
  Lean.SortMax1Var u   -> Set.singleton u
  Lean.SortMax1Vars us -> Set.fromList us

usedUniversesInTerm :: Lean.Term -> Set String
usedUniversesInTerm = \case
  Lean.Lambda bs t ->
    Set.unions (usedUniversesInTerm t : map usedUniversesInBinder bs)
  Lean.Pi bs t ->
    Set.unions (usedUniversesInTerm t : map usedUniversesInPiBinder bs)
  Lean.Let _ bs mty t b ->
    Set.unions
      [ Set.unions (map usedUniversesInBinder bs)
      , maybe Set.empty usedUniversesInTerm mty
      , usedUniversesInTerm t
      , usedUniversesInTerm b
      ]
  Lean.If c t f ->
    Set.unions [ usedUniversesInTerm c
               , usedUniversesInTerm t
               , usedUniversesInTerm f ]
  Lean.App f args ->
    Set.unions (usedUniversesInTerm f : map usedUniversesInTerm args)
  Lean.Sort s -> usedUniversesInSort s
  Lean.Var _ -> Set.empty
  Lean.ExplVar _ -> Set.empty
  Lean.Ascription a b ->
    Set.union (usedUniversesInTerm a) (usedUniversesInTerm b)
  Lean.NatLit _ -> Set.empty
  Lean.IntLit _ -> Set.empty
  Lean.List ts -> Set.unions (map usedUniversesInTerm ts)
  Lean.StringLit _ -> Set.empty
  Lean.Tactic _ -> Set.empty

-- | Produce a Lean term that represents a translation error inline
-- rather than failing the whole walk. Mirrors Rocq's @errorTermM@.
-- Useful for recursors over unmapped datatypes — the result is a
-- well-formed Lean value that points at where the problem is.
errorTermM :: TermTranslationMonad m => String -> m Lean.Term
errorTermM msg =
  pure $ Lean.App (Lean.Var (Lean.Ident "error")) [Lean.StringLit msg]

-- | Translate a 'FlatTermF' (atomic constructs of the SAWCore AST).
translateFTermF :: TermTranslationMonad m => FlatTermF Term -> m Lean.Term
translateFTermF ftf = case ftf of
  Sort s _h -> Lean.Sort <$> translateSort s

  -- @Foo#rec@ — SAWCore's eliminator. In Rocq this becomes @Foo_rect@;
  -- Lean's convention for an inductive @Foo@'s auto-generated
  -- eliminator is @Foo.rec@.
  --
  -- Always emit as @\@Foo.rec@ (explicit form). SAWCore's recursor
  -- arg list is @motive branch_1 … branch_n indices@, all positional
  -- and explicit; Lean's @Foo.rec@ marks the motive (and indices)
  -- implicit, so without @\@@ the positional SAW arg list would
  -- miss the motive slot. The instance-insertion concern that
  -- previously argued against @\@@ is gone now that we no longer
  -- auto-inject @[Inh_a : Inhabited a]@ binders on @isort@
  -- parameters.
  Recursor crec -> do
    let d     = recursorDataType crec
        dInfo = nameInfo d
    -- Guard the SAW-Nat / SAW-Pos mapping. We collapse those types
    -- to Lean's native 'Nat' at the 'SpecialTreatment' level and
    -- rely on 'leanOpaqueBuiltins' to keep every Prelude def whose
    -- RHS uses 'Nat#rec' / 'Pos#rec' opaque during normalization.
    -- If one still surfaces, the generated Lean would alias SAW's
    -- case order onto Lean's @Nat.rec@ (@zero, succ@) — a silent
    -- soundness divergence. Refuse with a clear error. See
    -- 'doc/2026-04-24_audit-nat-mapping.md'.
    let preludeNat = mkIdent preludeName "Nat"
        preludePos = mkIdent preludeName "Pos"
    case dInfo of
      ModuleIdentifier i
        | i == preludeNat -> Except.throwError (UnsoundRecursor "Nat")
        | i == preludePos -> Except.throwError (UnsoundRecursor "Pos")
      _ -> pure ()
    maybeDIdent <- case dInfo of
      ModuleIdentifier ident -> translateIdentToIdent ident
      ImportedName{}         -> pure Nothing
    case maybeDIdent of
      Just (Lean.Ident i) ->
        pure $ Lean.ExplVar (Lean.Ident (i ++ ".rec"))
      Nothing -> do
        let dName = Text.unpack (toAbsoluteName dInfo)
        errorTermM ("Recursor for " ++ dName ++
                    " cannot be translated: its datatype has no " ++
                    "fixed target on the Lean side.")

  -- Array literals. No bitvector specialization yet — the Rocq
  -- backend's `intToBv` collapse needs the full
  -- Data.BitVector.Sized / Data.Parameterized machinery, which we
  -- leave to a later pass.
  ArrayValue _ vec ->
    Lean.List <$> traverse translateTerm (toList vec)

  StringLit s -> pure (Lean.StringLit (Text.unpack s))

translateTerm :: TermTranslationMonad m => Term -> m Lean.Term
translateTerm t =
  case unwrapTermF t of

    FTermF ftf -> translateFTermF ftf

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
  Maybe ModuleName ->
    -- ^ the SAWCore module whose declarations are being translated,
    --   if any. References to other identifiers defined in this
    --   module are emitted unqualified.
  ModuleMap ->
  [Lean.Ident] ->
    -- ^ globals already translated (so we don't re-emit them as
    --   auxiliary @def@s when their bodies are referenced).
  [Lean.Ident] ->
    -- ^ local variables already in scope (e.g. the name of the
    --   definition being translated, to avoid shadowing).
  (forall m. TermTranslationMonad m => m a) ->
  Either TranslationError (a, TranslationState)
runTermTranslationMonad configuration mname mm globals localEnv =
  runTranslationMonad configuration
    (TranslationReader
       { _namedEnvironment  = Map.empty
       , _unavailableIdents = Set.unions [ reservedIdents
                                         , Set.fromList globals
                                         , Set.fromList localEnv
                                         ]
       , _sawModuleMap      = mm
       , _currentModule     = mname
       })
    (TranslationState
       { _globalDeclarations   = globals
       , _topLevelDeclarations = []
       , _universeVars         = Set.empty
       })

-- | Translate a SAWCore 'Term' and its type to a Lean @def@, together
-- with any auxiliary declarations needed to support it (the bodies of
-- constants referenced along the way).
--
-- Emits @noncomputable def@: SAWCore primitives like @coerce@,
-- @unsafeAssert@, @error@ are axioms that Lean's code generator
-- refuses to compile, and typical normalized terms reference at
-- least one of them. Marking every user def @noncomputable@ is a
-- safe over-approximation — the goal is a file that typechecks, not
-- one that runs.
translateDefDoc ::
  TranslationConfiguration ->
  ModuleMap ->
  Lean.Ident -> Term -> Term ->
  Either TranslationError (Doc ann)
translateDefDoc configuration mm name body tp = do
  ((body', tp'), state) <-
    runTermTranslationMonad configuration Nothing mm [] [name] $
      (,) <$> translateTerm body <*> translateTerm tp
  let auxDecls = reverse (view topLevelDeclarations state)
      univs    = Set.toAscList (view universeVars state)
      mainDecl = mkDefinitionWith Lean.Noncomputable univs name body' tp'
      -- Each 'prettyDecl' already ends with 'hardline'; 'vcat' adds
      -- another between elements, yielding one blank line between
      -- decls.
  pure $ if null auxDecls
    then Lean.prettyDecl mainDecl
    else vcat (map Lean.prettyDecl auxDecls) <> hardline <> Lean.prettyDecl mainDecl
