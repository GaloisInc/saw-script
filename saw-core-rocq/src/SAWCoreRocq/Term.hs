{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : SAWCoreRocq.Term
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module SAWCoreRocq.Term where

import           Control.Lens                 (makeLenses, over, set, to, view)
import           Control.Monad                (forM)
import qualified Control.Monad.Except         as Except
import qualified Control.Monad.Fail           as Fail
import           Control.Monad.Reader         (MonadReader(ask, local), asks)
import           Control.Monad.State          (MonadState(get), modify)
import           Data.Char                    (isDigit)
import           Data.IntMap.Strict           (IntMap)
import qualified Data.IntMap.Strict           as IntMap
import           Data.List                    (intersperse)
import           Data.Maybe                   (fromMaybe)
import qualified Data.Map                     as Map
import           Data.Map                     (Map)
import qualified Data.Set                     as Set
import           Data.Set                     (Set)
import qualified Data.Text                    as Text
import           Prelude                      hiding (fail)
import           Prettyprinter

import           Data.Parameterized.Pair
import           Data.Parameterized.NatRepr
import qualified Data.BitVector.Sized         as BV
import qualified Data.Vector                  as Vector (toList)
import qualified Language.Rocq.AST            as Rocq
import qualified Language.Rocq.Pretty         as Rocq

import           SAWCore.Module               (Def(..), ModuleMap, ResolvedName(..), requireNameInMap, resolvedNameType)
import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Pretty
import           SAWCore.Term.Functor
import           SAWCore.Term.Raw

import           SAWCoreRocq.Monad
import           SAWCoreRocq.SpecialTreatment

{-
import Debug.Trace
traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

-- | A Rocq identifier used for sharing subterms through let-bindings, annotated
-- with a 'Bool' flag indicating whether the shared subterm is closed, i.e., has
-- no free variables
data SharedName = SharedName { sharedNameIdent :: Rocq.Ident,
                               sharedNameIsClosed :: Bool }
                deriving Show

-- | The read-only state for translating terms
data TranslationReader = TranslationReader
  { _currentModule  :: Maybe ModuleName
    -- ^ The current Rocq module for the translation

  , _namedEnvironment  :: Map VarName Rocq.Ident
    -- ^ The map of Rocq identifiers associated with the SAW core named
    -- variables in scope

  , _unavailableIdents :: Set Rocq.Ident
    -- ^ The set of Rocq identifiers that are either reserved or already in use.
    -- To avoid shadowing, fresh identifiers should be chosen to be disjoint
    -- from this set.

  , _sharedNames :: IntMap SharedName
    -- ^ Index of identifiers for repeated subterms that have been lifted out
    -- into a let expression

  , _nextSharedName :: Rocq.Ident
    -- ^ The next available name to be used for a let-bound shared
    -- sub-expression

  , _sawModuleMap :: ModuleMap
    -- ^ The environment of SAW global definitions

  , _useImplicitBinders :: Bool
    -- ^ This is False when in a term context where using implicit binders
    -- doesn't make sense and are ignored by Rocq, such as inside lambda
    -- bodies, function arguments, etc.
  }
  -- deriving (Show)

makeLenses ''TranslationReader

data TranslationState = TranslationState

  { _globalDeclarations :: [Rocq.Ident]
    -- ^ Some Cryptol terms seem to capture the name and body of some functions
    -- they use (whether from the Cryptol prelude, or previously defined in the
    -- same file). We want to translate those exactly once, so we need to keep
    -- track of which ones have already been translated.

  , _topLevelDeclarations :: [Rocq.Decl]
    -- ^ Because some terms capture their dependencies, translating one term may
    -- result in multiple declarations: one for the term itself, but also zero
    -- or many for its dependencies. We store all of those in this, so that a
    -- caller of the translation may retrieve all the declarations needed to
    -- translate the term. The translation function itself will return only the
    -- declaration for the term being translated.

  }
  deriving (Show)

makeLenses ''TranslationState

-- | The constraint stating that 'm' can be used for term translation. This
-- requires that it have reader effects for 'TranslationReader' and state
-- effects for 'TranslationState'.
type TermTranslationMonad m =
  TranslationMonad TranslationReader TranslationState m

-- | Get just the 'TranslationReader' component of the reader value
askTR :: TermTranslationMonad m => m TranslationReader
askTR = otherConfiguration <$> ask

-- | Modify just the 'TranslationReader' component of the reader value
localTR :: TermTranslationMonad m =>
            (TranslationReader -> TranslationReader) -> m a -> m a
localTR f =
  local (\r -> r { otherConfiguration = f (otherConfiguration r) })

-- | Take a Rocq identifier that ends in a number (i.e., a sequence of digits)
-- and add 1 to that number, viewing an identifier with no trailing number as
-- ending in 0
nextVariant :: Rocq.Ident -> Rocq.Ident
nextVariant (Rocq.Ident s) = Rocq.Ident (reverse (go (reverse s)))
  where
    go :: String -> String
    go (c : cs)
      | c == '9'  = '0' : go cs
      | isDigit c = succ c : cs
    go cs = '1' : cs

-- | Find an fresh, as-yet-unused variant of the given Rocq identifier
freshVariant :: TermTranslationMonad m => Rocq.Ident -> m Rocq.Ident
freshVariant x =
  do used <- view unavailableIdents <$> askTR
     let ident0 = x
     let findVariant i = if Set.member i used then findVariant (nextVariant i) else i
     return $ findVariant ident0

-- | Locally mark a Rocq identifier as being used in the translation during a
-- translation computation, so that computation does not shadow it
withUsedRocqIdent :: TermTranslationMonad m => Rocq.Ident -> m a -> m a
withUsedRocqIdent ident m =
  localTR (over unavailableIdents (Set.insert ident)) m

-- | Translate a local name from a saw-core binder into a fresh Rocq identifier
translateLocalIdent :: TermTranslationMonad m => LocalName -> m Rocq.Ident
translateLocalIdent x = freshVariant (escapeIdent (Rocq.Ident (Text.unpack x)))

-- | Generate a fresh, unused Rocq identifier from a SAW core name and mark it as
-- unavailable in the supplied translation computation
withFreshIdent :: TermTranslationMonad m => LocalName -> (Rocq.Ident -> m a) ->
                  m a
withFreshIdent n f =
  do n_rocq <- translateLocalIdent n
     withUsedRocqIdent n_rocq $ f n_rocq

-- | Invalidate all shared subterms that are not closed in a translation
invalidateOpenSharing :: TermTranslationMonad m => m a -> m a
invalidateOpenSharing =
  localTR (over sharedNames $ IntMap.filter sharedNameIsClosed)

-- | Run a translation in a context with one more SAW core variable with the
-- given name. Pass the corresponding Rocq identifier used for this SAW core
-- variable to the computation in which it is bound.
withSAWVar :: TermTranslationMonad m => VarName -> (Rocq.Ident -> m a) -> m a
withSAWVar n m =
  withFreshIdent (vnName n) $ \n_rocq ->
  localTR (over namedEnvironment (Map.insert n n_rocq)) $ m n_rocq

-- | Find a fresh name generated from 'nextSharedName' to use in place of the
-- supplied 'Term' with the supplied index, and associate that index with the
-- fresh name in the 'sharedNames' sharing map. Pass the name that was generated
-- to the computation.
withSharedTerm :: TermTranslationMonad m => TermIndex -> Term ->
                  (Rocq.Ident -> m a) -> m a
withSharedTerm idx t f =
  do ident <- (view nextSharedName <$> askTR) >>= freshVariant
     let sh_nm = SharedName ident $ closedTerm t
     localTR (set nextSharedName (nextVariant ident) .
              over sharedNames (IntMap.insert idx sh_nm)) $
       withUsedRocqIdent ident $ f ident

-- | Use 'withSharedTerm' to mark a list of terms as being shared
withSharedTerms :: TermTranslationMonad m => [(TermIndex,Term)] ->
                   ([Rocq.Ident] -> m a) -> m a
withSharedTerms [] f = f []
withSharedTerms ((idx,t):ts) f =
  withSharedTerm idx t $ \n -> withSharedTerms ts $ \ns -> f (n:ns)


-- | The set of reserved identifiers in Rocq, obtained from section
-- \"Core language\" of the Rocq reference manual.
-- <https://rocq-prover.org/refman/language/core/basic.html>
reservedIdents :: Set Rocq.Ident
reservedIdents =
  Set.fromList $
  map Rocq.Ident $
  concatMap words $
  [ "_ Axiom CoFixpoint Definition Fixpoint Hypothesis IF Parameter Prop"
  , "SProp Set Theorem Type Variable as at by cofix discriminated else"
  , "end exists exists2 fix for forall fun if in lazymatch let match"
  , "multimatch return then using where with"
  ]

-- | Extract the list of names from a list of Rocq declarations.  Not all
-- declarations have names, e.g. comments and code snippets come without names.
namedDecls :: [Rocq.Decl] -> [Rocq.Ident]
namedDecls = concatMap filterNamed
  where
    filterNamed :: Rocq.Decl -> [Rocq.Ident]
    filterNamed (Rocq.Axiom n _)                                = [n]
    filterNamed (Rocq.Parameter n _)                            = [n]
    filterNamed (Rocq.Variable n _)                             = [n]
    filterNamed (Rocq.Comment _)                                = []
    filterNamed (Rocq.Definition n _ _ _)                       = [n]
    filterNamed (Rocq.InductiveDecl (Rocq.Inductive n _ _ _ _)) = [n]
    filterNamed (Rocq.Snippet _)                                = []
    filterNamed (Rocq.Section _ ds)                             = namedDecls ds

-- | Retrieve the names of all local and global declarations from the
-- translation state.
getNamesOfAllDeclarations ::
  TermTranslationMonad m =>
  m [Rocq.Ident]
getNamesOfAllDeclarations = view allDeclarations <$> get
  where
    allDeclarations =
      to (\ (TranslationState {..}) -> namedDecls _topLevelDeclarations ++ _globalDeclarations)

-- | Run a term translation computation
runTermTranslationMonad ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  [Rocq.Ident] ->
  [Rocq.Ident] ->
  (forall m. TermTranslationMonad m => m a) ->
  Either (TranslationError Term) (a, TranslationState)
runTermTranslationMonad configuration mname mm globalDecls localEnv =
  runTranslationMonad configuration
  (TranslationReader {
      _currentModule = mname
      , _namedEnvironment = Map.empty
      , _unavailableIdents  = Set.union reservedIdents (Set.fromList localEnv)
      , _sharedNames        = IntMap.empty
      , _nextSharedName     = "var__0"
      , _sawModuleMap       = mm
      , _useImplicitBinders = True })
  (TranslationState { _globalDeclarations = globalDecls
                    , _topLevelDeclarations  = []
                    })

-- | Return a Rocq term for an error computation with the given string message
errorTermM :: TermTranslationMonad m => String -> m Rocq.Term
errorTermM str = return $ Rocq.App (Rocq.Var "error") [Rocq.StringLit str]

qualify :: ModuleName -> Rocq.Ident -> Rocq.Ident
qualify m (Rocq.Ident i) = Rocq.Ident (Text.unpack (moduleNameText m) ++ "." ++ i)

-- | Translate an 'Ident' with a given list of arguments to a Rocq term, using
-- any special treatment for that identifier and qualifying it if necessary
translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Rocq.Term
translateIdentWithArgs i args = do
  currentModuleName <- asks (view currentModule . otherConfiguration)
  let identToRocq ident =
        if Just (identModule ident) == currentModuleName
          then base else qualify (translateModuleName (identModule ident)) base
        where
          base = escapeIdent (Rocq.Ident (identName ident))
  specialTreatment <- findSpecialTreatment i
  applySpecialTreatment identToRocq (atUseSite specialTreatment)

  where

    applySpecialTreatment identToRocq UsePreserve =
      Rocq.App (Rocq.Var $ identToRocq i) <$> mapM translateTerm args
    applySpecialTreatment _identToRocq (UseRename targetModule targetName expl) =
      Rocq.App
        ((if expl then Rocq.ExplVar else Rocq.Var) $
          qualify (fromMaybe (translateModuleName $ identModule i) targetModule)
          targetName)
          <$> mapM translateTerm args
    applySpecialTreatment _identToRocq (UseMacro n macroFun)
      | length args >= n
      , (m_args, args') <- splitAt n args =
        do f <- macroFun <$> mapM translateTerm m_args
           Rocq.App f <$> mapM translateTerm args'
    applySpecialTreatment _identToRocq (UseMacro n _) =
      errorTermM (unwords
        [ "Identifier"
        , show i
        , "not applied to required number of args, which is"
        , show n
        ]
      )

-- | Helper for 'translateIdentWithArgs' with no arguments
translateIdent :: TermTranslationMonad m => Ident -> m Rocq.Term
translateIdent i = translateIdentWithArgs i []

-- | Translate a constant to a Rocq term. If the constant is named with
-- an 'Ident', then it already has a top-level translation from
-- translating the SAW core module containing that 'Ident'. If the
-- constant is an 'ImportedName', however, then it might not have a
-- Rocq definition already, so add a definition of it to the top-level
-- translation state.
translateConstant :: TermTranslationMonad m => Name -> m Rocq.Term
translateConstant nm
  | ModuleIdentifier ident <- nameInfo nm = translateIdent ident
translateConstant nm =
  do -- First, apply the constant renaming to get the name for this constant
     configuration <- asks translationConfiguration
     -- TODO short name seems wrong
     let nm_str = Text.unpack $ toShortName $ nameInfo nm
     let renamed =
           escapeIdent $ Rocq.Ident $ fromMaybe nm_str $
           lookup nm_str $ constantRenaming configuration

     -- Next, test if we should add a definition of this constant
     alreadyTranslatedDecls <- getNamesOfAllDeclarations
     let skip_def =
           elem renamed alreadyTranslatedDecls ||
           elem nm_str (constantSkips configuration)

     -- Add the definition if we aren't skipping it
     mm <- asks (view sawModuleMap . otherConfiguration)
     let resolved = requireNameInMap nm mm
     let maybe_body =
           case resolved of
             ResolvedDef d -> defBody d
             _ -> Nothing
     case maybe_body of
       _ | skip_def -> return ()
       Just body ->
         -- If the definition has a body, add it as a definition
         do b <- withTopTranslationState $ translateTermLet body
            tp <- withTopTranslationState $ translateTermLet (resolvedNameType resolved)
            modify $ over topLevelDeclarations $ (mkDefinition renamed b tp :)
       Nothing ->
         -- If not, add it as a Rocq Variable declaration
         do tp <- withTopTranslationState $ translateTermLet (resolvedNameType resolved)
            modify (over topLevelDeclarations (Rocq.Variable renamed tp :))

     -- Finally, return the constant as a Rocq variable
     pure (Rocq.Var renamed)


-- | Translate an 'Ident' and see if the result maps to a special 'Rocq.Ident',
-- returning the latter 'Rocq.Ident' if so
translateIdentToIdent :: TermTranslationMonad m => Ident -> m (Maybe Rocq.Ident)
translateIdentToIdent i =
  (atUseSite <$> findSpecialTreatment i) >>= \case
    UsePreserve -> return $ Just (qualify translatedModuleName (Rocq.Ident (Text.unpack (identBaseName i))))
    UseRename   targetModule targetName _ ->
      return $ Just $ qualify (fromMaybe translatedModuleName targetModule) targetName
    UseMacro _ _ -> return Nothing
  where
    translatedModuleName = translateModuleName (identModule i)

translateSort :: Sort -> Rocq.Sort
translateSort s = if s == propSort then Rocq.Prop else Rocq.Type

flatTermFToExpr ::
  TermTranslationMonad m =>
  FlatTermF Term ->
  m Rocq.Term
flatTermFToExpr tf = -- traceFTermF "flatTermFToExpr" tf $
  case tf of
    PairValue x y -> Rocq.App (Rocq.Var "pair") <$> traverse translateTerm [x, y]
    PairType x y  -> Rocq.App (Rocq.Var "prod") <$> traverse translateTerm [x, y]
    PairLeft t    ->
      Rocq.App <$> pure (Rocq.Var "fst") <*> traverse translateTerm [t]
    PairRight t   ->
      Rocq.App <$> pure (Rocq.Var "snd") <*> traverse translateTerm [t]

    Recursor crec ->
      do let d = recursorDataType crec
         maybe_d_trans <-
           case nameInfo d of
             ModuleIdentifier ident -> translateIdentToIdent ident
             ImportedName{} -> pure Nothing
         case maybe_d_trans of
           Just (Rocq.Ident i) -> return $ Rocq.ExplVar (Rocq.Ident (i ++ "_rect"))
           Nothing ->
             errorTermM ("Recursor for " ++ show d ++
                         " cannot be translated because the datatype " ++
                         "is mapped to an arbitrary Rocq term")

    Sort s _h -> pure (Rocq.Sort (translateSort s))
    ArrayValue (asBoolType -> Just ()) (traverse asBool -> Just bits)
      | Pair w bv <- BV.bitsBE (Vector.toList bits)
      , Left LeqProof <- decideLeq (knownNat @1) w -> do
          return (Rocq.App (Rocq.Var "intToBv")
                  [Rocq.NatLit (intValue w), Rocq.ZLit (BV.asSigned w bv)])
    ArrayValue _ vec -> do
      elems <- Vector.toList <$> mapM translateTerm vec
      -- NOTE: with VectorNotations, this is actually a Rocq vector literal
      return $ Rocq.List elems
    StringLit s -> pure (Rocq.Scope (Rocq.StringLit (Text.unpack s)) "string")


-- | Recognizes an @App (App "Cryptol.seq" n) x@ and returns @(n, x)@.
asSeq :: Recognizer Term (Term, Term)
asSeq t = do (f, args) <- asApplyAllRecognizer t
             fid <- asGlobalDef f
             case (fid, args) of
               ("Cryptol.seq", [n, x]) -> return (n,x)
               _ -> Fail.fail "not a seq"

asApplyAllRecognizer :: Recognizer Term (Term, [Term])
asApplyAllRecognizer t = do _ <- asApp t
                            return $ asApplyAll t

-- | Run a translation in the top-level translation state with no free SAW
-- variables and no bound Rocq identifiers
withTopTranslationState :: TermTranslationMonad m => m a -> m a
withTopTranslationState m =
  localTR (\r ->
            TranslationReader {
              _currentModule      = view currentModule r,
              _namedEnvironment   = Map.empty,
              _unavailableIdents  = reservedIdents,
              _sharedNames        = IntMap.empty,
              _nextSharedName     = "var__0" ,
              _sawModuleMap       = view sawModuleMap r,
              _useImplicitBinders = True }) m

-- | Generate a Rocq @Definition@ with a given name, body, and type, using the
-- lambda-bound variable names for the variables if they are available
mkDefinition :: Rocq.Ident -> Rocq.Term -> Rocq.Term -> Rocq.Decl
mkDefinition name (Rocq.Lambda bs t) (Rocq.Pi bs' tp)
  | length bs' == length bs =
    -- NOTE: there are a number of cases where length bs /= length bs', such as
    -- where the type of a definition is computed from some input (so might not
    -- have any explicit pi-abstractions), or where the body of a definition is
    -- a partially applied function (so might not have any lambdas). We could in
    -- theory try to handle these more complex cases by assigning names to some
    -- of the arguments, but it's not really necessary for the translation to be
    -- correct, so we just do the simple thing here.
    Rocq.Definition name (zipWith combineBinders bs bs') (Just tp) t
mkDefinition name t tp = Rocq.Definition name [] (Just tp) t

-- | Combine a term-level Binder with a type-level PiBinder, taking the name
-- and type from the Binder but the implicit/explicit status from the PiBinder.
combineBinders :: Rocq.Binder -> Rocq.PiBinder -> Rocq.Binder
combineBinders (Rocq.Binder _ n mty) (Rocq.PiBinder impl _ _) = Rocq.Binder impl n mty

mkLet :: (Rocq.Ident, Rocq.Term) -> Rocq.Term -> Rocq.Term
mkLet (name, rhs) body = Rocq.Let name [] Nothing rhs body

implicit :: Bool -> Rocq.BinderImplicity
implicit useImplicits = if useImplicits then Rocq.Implicit else Rocq.Explicit

-- | The result of translating a SAW core variable binding to Rocq, including the
-- Rocq identifier for the variable, the Rocq translation of its type, and 0 or
-- more implicit Rocq arguments that apply to the variable
data BindTrans = BindTrans { bindTransIdent :: Rocq.Ident,
                             bindTransType :: Rocq.Type,
                             bindTransImps :: [(Rocq.Ident,Rocq.Type)] }

-- | Convert a 'BindTrans' to a list of Rocq term-level binders
bindTransToBinder :: Bool -> BindTrans -> [Rocq.Binder]
bindTransToBinder useImplicits (BindTrans {..}) =
  Rocq.Binder Rocq.Explicit bindTransIdent (Just bindTransType) :
  map (\(n,ty) -> Rocq.Binder (implicit useImplicits) n (Just ty)) bindTransImps

-- | Convert a 'BindTrans' to a list of Rocq type-level pi-abstraction binders.
bindTransToPiBinder :: Bool -> BindTrans -> [Rocq.PiBinder]
bindTransToPiBinder useImplicits (BindTrans { .. }) =
  case bindTransImps of
    [] | bindTransIdent == "_" -> [Rocq.PiBinder Rocq.Explicit Nothing bindTransType]
    [] -> [Rocq.PiBinder Rocq.Explicit (Just bindTransIdent) bindTransType]
    _ ->
      Rocq.PiBinder Rocq.Explicit (Just bindTransIdent) bindTransType :
      map (\(n,ty) -> Rocq.PiBinder (implicit useImplicits) (Just n) ty) bindTransImps

-- | Given a 'VarName' and its type (as a 'Term'), translate the 'VarName'
-- to a Rocq identifier, translate the type to a Rocq term, and generate zero or
-- more additional 'Ident's and 'Type's representing additonal implicit
-- typeclass arguments, added if the given type is @isort@, etc. Pass all of
-- this information to the supplied computation, in which the SAW core variable
-- is bound to its Rocq identifier.
translateBinder :: TermTranslationMonad m => VarName -> Term ->
                   (BindTrans -> m a) -> m a
translateBinder vn ty@(asPiList -> (args, pi_body)) f =
  do ty' <- translateTerm ty
     let mb_sort = asSortWithFlags pi_body
         flagValues = sortFlagsToList $ maybe noFlags snd mb_sort
         flagLocalNames = [("Inh", "SAWCoreScaffolding.Inhabited"),
                           ("QT", "QuantType")]
     withSAWVar vn $ \n' ->
       helper n' (zip flagValues flagLocalNames) (\imps ->
                                                   f $ BindTrans n' ty' imps)
       where
         n = vnName vn
         helper _ [] g = g []
         helper n' ((True,(prefix,tc)):rest) g =
           do nhty <- translateImplicitHyp (Rocq.Var tc) args (Rocq.Var n')
              withFreshIdent (prefix <> "_" <> n) $ \nh ->
                helper n' rest (g . ((nh,nhty) :))
         helper n' ((False,_):rest) g = helper n' rest g

-- | Call 'translateBinder' on a list of SAW core bindings
translateBinders :: TermTranslationMonad m => [(VarName,Term)] ->
                    ([BindTrans] -> m a) -> m a
translateBinders [] f = f []
translateBinders ((n,ty):ns_tys) f =
  translateBinder n ty $ \bnd ->
  translateBinders ns_tys $ \bnds -> f (bnd : bnds)

-- | Given a typeclass (as a Rocq term), a list of 'LocalName's and their
-- corresponding types (as 'Term's), and a type-level function with argument
-- types given by the prior list, return a 'Pi' of the given arguments, inside
-- of which is an 'App' of the typeclass to the fully-applied type-level
-- function
translateImplicitHyp ::
  TermTranslationMonad m =>
  Rocq.Term -> [(VarName, Term)] -> Rocq.Term -> m Rocq.Term
translateImplicitHyp tc [] tm = return (Rocq.App tc [tm])
translateImplicitHyp tc args tm = do
  useImplicits <- view useImplicitBinders <$> askTR
  translateBinders args $ \args' ->
    return $ Rocq.Pi (concatMap (mkPi useImplicits) args') (Rocq.App tc [Rocq.App tm (map mkArg args')])
  where
    mkPi useImplicits (BindTrans nm ty nhs) =
      Rocq.PiBinder Rocq.Explicit (Just nm) ty :
      map (\(nh,nhty) -> Rocq.PiBinder (implicit useImplicits) (Just nh) nhty) nhs
    mkArg b = Rocq.Var $ bindTransIdent b

-- | Given a list of 'LocalName's and their corresponding types (as 'Term's),
-- return a list of 'Binder's, for use representing the bound variables
-- in 'Lambda's, 'Let's, etc.
translateParams :: TermTranslationMonad m => [(VarName, Term)] ->
                   ([Rocq.Binder] -> m a) -> m a
translateParams bs m = do
  useImplicits <- view useImplicitBinders <$> askTR
  translateBinders bs (m . concat . map (bindTransToBinder useImplicits))

-- | Given a list of 'VarName's and their corresponding types (as 'Term's)
-- representing argument types and a 'Term' representing the return type,
-- return the resulting 'Pi', with additional implicit arguments added after
-- each instance of @isort@, @qsort@, etc.
translatePi :: TermTranslationMonad m => [(VarName, Term)] -> Term -> m Rocq.Term
translatePi binders body =
  translatePiBinders binders $ \bindersT ->
  do bodyT <- translateTermLet body
     return $ Rocq.Pi bindersT bodyT

-- | Given a 'LocalName' and its type (as a 'Term'), return an explicit
-- 'PiBinder' followed by zero or more implicit 'PiBinder's representing
-- additonal implicit typeclass arguments, added if the given type is @isort@,
-- @qsort@, etc.
translatePiBinders :: TermTranslationMonad m => [(VarName, Term)] ->
                      ([Rocq.PiBinder] -> m a) -> m a
translatePiBinders bs m = do
  useImplicits <- view useImplicitBinders <$> askTR
  translateBinders bs (m . concat . map (bindTransToPiBinder useImplicits))

-- | Find all subterms of a SAW core term that should be shared, and generate
-- let-bindings in Rocq to bind them to local variables. Translate SAW core term
-- using those let-bindings for the shared subterms.
translateTermLet :: TermTranslationMonad m => Term -> m Rocq.Term
translateTermLet t =
  let occ_map = scTermCount False t
      shares = IntMap.assocs $ fmap fst $ IntMap.filter keep occ_map
      share_tms = map snd shares in
  -- NOTE: larger terms always have later stAppIndices than their subterms, so
  -- IntMap.assocs above is guaranteed to return subterms before superterms;
  -- this ensures that the right-hand sides in our nested let-bindings below
  -- only refer to variables bound earlier, not later
  withSharedTerms shares $ \names ->
  do defs <- traverse translateTermUnshared share_tms
     body <- translateTerm t
     pure (foldr mkLet body $ zip names defs)
  where
    keep (t', n) = n > 1 && shouldMemoizeTerm t'

-- | Translate a SAW core 'Term' to Rocq, using let-bound Rocq names when they are
-- associated with the given term for sharing
translateTerm :: TermTranslationMonad m => Term -> m Rocq.Term
translateTerm t =
  case t of
    STApp { stAppIndex = i } ->
      do shared <- view sharedNames <$> askTR
         case IntMap.lookup i shared of
           Nothing -> translateTermUnshared t
           Just sh -> pure (Rocq.Var $ sharedNameIdent sh)

-- | Translate a SAW core 'Term' to Rocq without using sharing
translateTermUnshared :: TermTranslationMonad m => Term -> m Rocq.Term
translateTermUnshared t =
  -- traceTerm "translateTerm" t $
  case unwrapTermF t of

    FTermF ftf -> flatTermFToExpr ftf

    Pi {} ->
      let (params, e) = asPiList t in
      translatePi params e

    Lambda {} ->
      let (params, e) = asLambdaList t in
      localTR (set useImplicitBinders False) $
        translateParams params $ \paramTerms ->
        do e' <- translateTermLet e
           return (Rocq.Lambda paramTerms e')

    App {} ->
      -- asApplyAll: innermost argument first
      let (f, args) = asApplyAll t
      in
      case f of
      (asGlobalDef -> Just i) ->
        case i of
        "Prelude.natToInt" ->
          case args of
          [n] -> translateTerm n >>= \case
            Rocq.NatLit n' -> pure $ Rocq.ZLit n'
            _ -> translateIdentWithArgs "Prelude.natToInt" [n]
          _ -> badTerm
        "Prelude.intNeg" ->
          case args of
          [z] -> translateTerm z >>= \case
            Rocq.ZLit z' -> pure $ Rocq.ZLit (-z')
            _ -> translateIdentWithArgs "Prelude.intNeg" [z]
          _ -> badTerm
        "Prelude.ite" ->
          case args of
          -- `rest` can be non-empty in examples like:
          -- (if b then f else g) arg1 arg2
          _ty : c : tt : ft : rest -> do
            ite <- Rocq.If <$> translateTerm c <*> translateTerm tt <*> translateTerm ft
            case rest of
              [] -> return ite
              _  -> Rocq.App ite <$> mapM translateTerm rest
          -- When `ite` is partially applied (fewer than 4 args), fall
          -- through to `translateIdentWithArgs` to translate it as a
          -- normal function application instead of if-then-else syntax.
          _ -> translateIdentWithArgs i args

        -- Refuse to translate any recursive value defined using Prelude.fix
        "Prelude.fix" -> badTerm

        _ -> translateIdentWithArgs i args
      _ -> Rocq.App <$> translateTerm f <*> traverse translateTerm args

    -- Constants
    Constant n -> translateConstant n

    Variable nm _tp ->
      do nenv <- view namedEnvironment <$> askTR
         case Map.lookup nm nenv of
           Just ident -> pure (Rocq.Var ident)
           Nothing ->
             do let nm_str = Text.unpack $ vnName nm
                let ident = escapeIdent $ Rocq.Ident $ nm_str
                pure (Rocq.Var ident)

  where
    badTerm          = Except.throwError $ BadTerm t

-- | In order to turn fixpoint computations into iterative computations, we need
-- to be able to create \"dummy\" values at the type of the computation.
defaultTermForType ::
  TermTranslationMonad m =>
  Term -> m Rocq.Term
defaultTermForType typ = do
  case typ of
    (asBoolType -> Just ()) -> translateIdent (mkIdent preludeName "False")

    (isGlobalDef "Prelude.Nat" -> Just ()) -> return $ Rocq.NatLit 0

    (asIntegerType -> Just ()) -> return $ Rocq.ZLit 0

    (asSeq -> Just (n, typ')) -> do
      seqConst <- translateIdent (mkIdent (mkModuleName ["Cryptol"]) "seqConst")
      nT       <- translateTerm n
      typ'T    <- translateTerm typ'
      defaultT <- defaultTermForType typ'
      return $ Rocq.App seqConst [ nT, typ'T, defaultT ]

    (asPairType -> Just (x,y)) -> do
      x' <- defaultTermForType x
      y' <- defaultTermForType y
      return $ Rocq.App (Rocq.Var "pair") [x',y']

    (asPiList -> (bs,body))
      | not (null bs)
      , closedTerm body ->
      do bs'   <- forM bs $ \ (_nm, ty) -> Rocq.Binder Rocq.Explicit "_" . Just <$> translateTerm ty
         body' <- defaultTermForType body
         return $ Rocq.Lambda bs' body'

    _ -> Except.throwError $ CannotCreateDefaultValue typ

-- | Translate a SAW core term along with its type to a Rocq term and its Rocq
-- type, and pass the results to the supplied function
translateTermToDocWith ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  [Rocq.Ident] -> -- ^ globals that have already been translated
  [Rocq.Ident] -> -- ^ names of local variables in scope
  (Rocq.Term -> Rocq.Term -> Doc ann) ->
  Term -> Term ->
  Either (TranslationError Term) (Doc ann)
translateTermToDocWith configuration r mm globalDecls localEnv f t tp_trm = do
  ((term, tp), state) <-
    runTermTranslationMonad configuration r mm globalDecls localEnv
    ((,) <$> translateTermLet t <*> translateTermLet tp_trm)
  let decls = view topLevelDeclarations state
  return $
    vcat $
    [ (vcat . intersperse hardline . map Rocq.prettyDecl . reverse) decls
    , if null decls then mempty else hardline
    , f term tp
    ]

-- | Translate a SAW core 'Term' and its type (given as a 'Term') to a Rocq
-- definition with the supplied name
translateDefDoc ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  [Rocq.Ident] ->
  Rocq.Ident -> Term -> Term ->
  Either (TranslationError Term) (Doc ann)
translateDefDoc configuration r mm globalDecls name =
  translateTermToDocWith configuration r mm globalDecls [name]
  (\ t tp -> Rocq.prettyDecl $ mkDefinition name t tp)
