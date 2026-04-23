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
import           Control.Monad.State          (MonadState(get), modify)
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

import           SAWCore.Module               (Ctor(..), Def(..), ModuleMap,
                                               ResolvedName(..),
                                               requireNameInMap, resolveNameInMap,
                                               resolvedNameType)
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
-- SAWCore's @sort 0@ is the universe of regular data types; it
-- translates to Lean's concrete @Type@ (@Type 0@). SAWCore's higher
-- sorts (@sort k@ for k ≥ 1) translate to universe-polymorphic
-- @Sort u{k}@, with the universe variables recorded in
-- 'universeVars' so the surrounding declaration can list them.
--
-- Rationale: SAWCore uses @sort 1@ only as the type of things that
-- /contain/ values at arbitrary levels (e.g. the type-parameter
-- @t : sort 1@ in @Eq : (t : sort 1) -&gt; t -&gt; t -&gt; Prop@). Keeping
-- that use-site polymorphic lets Lean unify @t@ with @Prop@,
-- @Type 0@, or a user-supplied @Type m@ as needed.
translateSort :: TermTranslationMonad m => Sort -> m Lean.Sort
translateSort s
  | s == propSort = pure Lean.Prop
  | otherwise = case s of
      TypeSort 0 -> pure Lean.Type
      TypeSort n -> do
        let uname = "u" ++ show (fromIntegral n :: Integer)
        modify (over universeVars (Set.insert uname))
        pure (Lean.SortVar uname)
      _ -> pure Lean.Type  -- unreachable; propSort case handled above

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

-- | The Lean-side type of the @Inhabited@ typeclass. Use sites get an
-- '[Inh_a : Inhabited a]' instance binder; Lean's instance search
-- fills it in at call sites.
inhabitedModuleIdent :: Lean.Ident
inhabitedModuleIdent = Lean.Ident "CryptolToLean.SAWCoreScaffolding.Inhabited"

-- | The result of translating a SAWCore binder to Lean: the Lean
-- identifier, the translated type, and zero-or-more auxiliary
-- instance arguments (one per SAWCore sort flag set on the binder's
-- type). Mirrors @SAWCoreRocq.Term.BindTrans@.
data BindTrans = BindTrans
  Lean.Ident                  -- ^ the translated binder name
  Lean.Type                   -- ^ the translated binder type
  [(Lean.Ident, Lean.Type)]   -- ^ auxiliary instance arguments

-- | Project the translated identifier out of a 'BindTrans' — used
-- when the argument list is needed at an instance-hypothesis
-- application site.
bindTransIdent :: BindTrans -> Lean.Ident
bindTransIdent (BindTrans n _ _) = n

-- | Flatten a 'BindTrans' into a list of Lean term-level 'Binder's.
-- The main variable is explicit; each auxiliary hypothesis is an
-- 'Instance' binder (@[Inh_a : Inhabited a]@) so Lean's typeclass
-- search can fill it in at call sites.
bindTransToBinder :: BindTrans -> [Lean.Binder]
bindTransToBinder (BindTrans name ty imps) =
  Lean.Binder Lean.Explicit name (Just ty) :
  map (\(n, t) -> Lean.Binder Lean.Instance n (Just t)) imps

-- | Flatten a 'BindTrans' into a list of Lean type-level 'PiBinder's.
-- Anonymous variables (named @_@ in SAWCore) with no auxiliary
-- hypotheses collapse to the @A -> rest@ arrow form.
bindTransToPiBinder :: BindTrans -> [Lean.PiBinder]
bindTransToPiBinder (BindTrans name ty imps) =
  case imps of
    [] | name == Lean.Ident "_" ->
        [Lean.PiBinder Lean.Explicit Nothing ty]
    [] ->
        [Lean.PiBinder Lean.Explicit (Just name) ty]
    _ ->
        Lean.PiBinder Lean.Explicit (Just name) ty :
        map (\(n, t) -> Lean.PiBinder Lean.Instance (Just n) t) imps

-- | Build the type of an auxiliary instance hypothesis for a binder
-- whose SAWCore type has the @isort@ flag set. Given:
--
-- * a Lean type constructor @tc@ (e.g. @Inhabited@)
-- * the @args@ appearing in the binder's pi-list (inner binders, if
--   the binder is itself a pi type), translated
-- * the head term @tm@ the constructor is being applied to
--
-- produces the Lean type @(x1 : A1) -> ... -> tc (tm x1 ... xn)@.
-- Mirrors @SAWCoreRocq.Term.translateImplicitHyp@ but always uses
-- explicit pi binders on the inner args (Lean's typeclass search
-- works across them without needing implicit markings).
translateImplicitHyp ::
  TermTranslationMonad m =>
  Lean.Term -> [(VarName, Term)] -> Lean.Term -> m Lean.Term
translateImplicitHyp tc [] tm = pure (Lean.App tc [tm])
translateImplicitHyp tc args tm =
  translateBinders' args $ \args' ->
    pure $ Lean.Pi (concatMap mkPi args')
                   (Lean.App tc [Lean.App tm (map mkArg args')])
  where
    mkPi (BindTrans n ty imps) =
      Lean.PiBinder Lean.Explicit (Just n) ty :
      map (\(nh, ty') -> Lean.PiBinder Lean.Instance (Just nh) ty') imps
    mkArg b = Lean.Var (bindTransIdent b)

-- | Translate a single SAW-core binder. If the binder's /return/ type
-- carries the @isort@ SAWCore sort flag, an extra @[Inh_a : Inhabited
-- a]@ instance hypothesis is produced alongside. The 'qsort' flag is
-- not (yet) handled — see the 'CryptolToLean.SAWCoreScaffolding'
-- scaffolding for the long-term plan.
translateBinder' :: TermTranslationMonad m => VarName -> Term ->
                    (BindTrans -> m a) -> m a
translateBinder' vn ty f = do
  ty' <- translateTerm ty
  let (args, piBody) = asPiList ty
      isISort = case asSortWithFlags piBody of
        Just (_, flags) -> case sortFlagsToList flags of
                             (i : _) -> i
                             _       -> False
        Nothing -> False
  withSAWVar vn $ \n' ->
    if isISort
      then do
        hypTy <- translateImplicitHyp (Lean.Var inhabitedModuleIdent) args
                                      (Lean.Var n')
        let hypBaseName = Lean.Ident ("Inh_" ++ Text.unpack (vnName vn))
        hypName <- freshVariant hypBaseName
        withUsedLeanIdent hypName $
          f (BindTrans n' ty' [(hypName, hypTy)])
      else
        f (BindTrans n' ty' [])

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
  pure $ case treatment of
    UsePreserve -> Just qualifiedIdent
    UseRename mTargetMod targetName _ ->
      Just $ maybe targetName (`qualify` targetName) mTargetMod
    UseMacro _ _ -> Nothing

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
    apply _ _ (UseRename mTargetMod targetName expl) =
      let qualifiedName = maybe targetName (`qualify` targetName) mTargetMod
          head_ = (if expl then Lean.ExplVar else Lean.Var) qualifiedName
      in
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
          modify (over topLevelDeclarations (Lean.Axiom [] renamed tp :))

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
    one (Lean.Axiom _ n _)                                = [n]
    one (Lean.Variable n _)                               = [n]
    one (Lean.Definition _ _ n _ _ _)                     = [n]
    one (Lean.InductiveDecl (Lean.Inductive _ n _ _ _ _)) = [n]
    one (Lean.Namespace _ ds)                             = namedDecls ds
    one (Lean.Comment _)                                  = []
    one (Lean.Snippet _)                                  = []

-- | Run a sub-translation in a fresh local scope (empty variable
-- environment). Used when pulling in a constant's body — the body is
-- closed, so no outer bindings should leak in. The outer
-- 'unavailableIdents' set is preserved so a translated body can't
-- pick a fresh name that shadows an outer def already being emitted.
withTopTranslationState :: TermTranslationMonad m => m a -> m a
withTopTranslationState = localTR $ \r ->
  TranslationReader
    { _namedEnvironment  = Map.empty
    , _unavailableIdents = view unavailableIdents r
    , _sawModuleMap      = view sawModuleMap r
    , _currentModule     = view currentModule r
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
-- body and type may reference.
mkDefinitionWith ::
  Lean.Noncomputable -> [String] ->
  Lean.Ident -> Lean.Term -> Lean.Term -> Lean.Decl
mkDefinitionWith nc univs name (Lean.Lambda bs t) (Lean.Pi bs' tp)
  | length bs' == length bs =
      Lean.Definition nc univs name (zipWith combineBinders bs bs') (Just tp) t
mkDefinitionWith nc univs name t tp =
  Lean.Definition nc univs name [] (Just tp) t

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
  Recursor crec -> do
    let d = recursorDataType crec
    maybeDIdent <- case nameInfo d of
      ModuleIdentifier ident -> translateIdentToIdent ident
      ImportedName{}         -> pure Nothing
    case maybeDIdent of
      Just (Lean.Ident i) ->
        pure $ Lean.ExplVar (Lean.Ident (i ++ ".rec"))
      Nothing -> do
        let dName = Text.unpack (toAbsoluteName (nameInfo d))
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
      mainDecl = mkDefinitionWith Lean.Computable univs name body' tp'
      -- Each 'prettyDecl' already ends with 'hardline'; 'vcat' adds
      -- another between elements, yielding one blank line between
      -- decls.
  pure $ if null auxDecls
    then Lean.prettyDecl mainDecl
    else vcat (map Lean.prettyDecl auxDecls) <> hardline <> Lean.prettyDecl mainDecl
