{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

{- |
Module      : SAWCoreCoq.Term
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module SAWCoreCoq.Term where

import           Control.Lens                                  (makeLenses, over, set, to, view)
import           Control.Monad                                 (forM)
import qualified Control.Monad.Except                          as Except
import qualified Control.Monad.Fail                            as Fail
import           Control.Monad.Reader                          (MonadReader(ask, local), asks)
import           Control.Monad.State                           (MonadState(get), modify)
import           Data.Char                                     (isDigit)
import           Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict                            as IntMap
import           Data.List                                     (intersperse, sortOn)
import           Data.Maybe                                    (fromMaybe)
import qualified Data.Map                                      as Map
import           Data.Map (Map)
import qualified Data.Set                                      as Set
import           Data.Set (Set)
import qualified Data.Text                                     as Text
import           Prelude                                       hiding (fail)
import           Prettyprinter

import           Data.Parameterized.Pair
import           Data.Parameterized.NatRepr
import qualified Data.BitVector.Sized                          as BV
import qualified Data.Vector                                   as Vector (toList)
import qualified Language.Coq.AST                              as Coq
import qualified Language.Coq.Pretty                           as Coq

import           SAWCore.Module (Def(..), ModuleMap, ResolvedName(..), requireNameInMap, resolvedNameType)
import           SAWCore.Name
import           SAWCore.Recognizer
import           SAWCore.SharedTerm
import           SAWCore.Term.Pretty
import           SAWCore.Term.Functor
import           SAWCore.Term.Raw

import           SAWCoreCoq.Monad
import           SAWCoreCoq.SpecialTreatment

{-
import Debug.Trace
traceTerm :: String -> Term -> a -> a
traceTerm ctx t a = trace (ctx ++ ": " ++ showTerm t) a
-}

-- | A Coq identifier used for sharing subterms through let-bindings, annotated
-- with a 'Bool' flag indicating whether the shared subterm is closed, i.e., has
-- no free variables
data SharedName = SharedName { sharedNameIdent :: Coq.Ident,
                               sharedNameIsClosed :: Bool }
                deriving Show

-- | The read-only state for translating terms
data TranslationReader = TranslationReader
  { _currentModule  :: Maybe ModuleName
    -- ^ The current Coq module for the translation

  , _namedEnvironment  :: Map VarName Coq.Ident
    -- ^ The map of Coq identifiers associated with the SAW core named
    -- variables in scope

  , _unavailableIdents :: Set Coq.Ident
    -- ^ The set of Coq identifiers that are either reserved or already in use.
    -- To avoid shadowing, fresh identifiers should be chosen to be disjoint
    -- from this set.

  , _sharedNames :: IntMap SharedName
    -- ^ Index of identifiers for repeated subterms that have been lifted out
    -- into a let expression

  , _nextSharedName :: Coq.Ident
    -- ^ The next available name to be used for a let-bound shared
    -- sub-expression

  , _sawModuleMap :: ModuleMap
    -- ^ The environment of SAW global definitions
  }
  -- deriving (Show)

makeLenses ''TranslationReader

data TranslationState = TranslationState

  { _globalDeclarations :: [Coq.Ident]
    -- ^ Some Cryptol terms seem to capture the name and body of some functions
    -- they use (whether from the Cryptol prelude, or previously defined in the
    -- same file). We want to translate those exactly once, so we need to keep
    -- track of which ones have already been translated.

  , _topLevelDeclarations :: [Coq.Decl]
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

-- | Take a Coq identifier that ends in a number (i.e., a sequence of digits)
-- and add 1 to that number, viewing an identifier with no trailing number as
-- ending in 0
nextVariant :: Coq.Ident -> Coq.Ident
nextVariant (Coq.Ident s) = Coq.Ident (reverse (go (reverse s)))
  where
    go :: String -> String
    go (c : cs)
      | c == '9'  = '0' : go cs
      | isDigit c = succ c : cs
    go cs = '1' : cs

-- | Find an fresh, as-yet-unused variant of the given Coq identifier
freshVariant :: TermTranslationMonad m => Coq.Ident -> m Coq.Ident
freshVariant x =
  do used <- view unavailableIdents <$> askTR
     let ident0 = x
     let findVariant i = if Set.member i used then findVariant (nextVariant i) else i
     return $ findVariant ident0

-- | Locally mark a Coq identifier as being used in the translation during a
-- translation computation, so that computation does not shadow it
withUsedCoqIdent :: TermTranslationMonad m => Coq.Ident -> m a -> m a
withUsedCoqIdent ident m =
  localTR (over unavailableIdents (Set.insert ident)) m

-- | Translate a local name from a saw-core binder into a fresh Coq identifier
translateLocalIdent :: TermTranslationMonad m => LocalName -> m Coq.Ident
translateLocalIdent x = freshVariant (escapeIdent (Coq.Ident (Text.unpack x)))

-- | Generate a fresh, unused Coq identifier from a SAW core name and mark it as
-- unavailable in the supplied translation computation
withFreshIdent :: TermTranslationMonad m => LocalName -> (Coq.Ident -> m a) ->
                  m a
withFreshIdent n f =
  do n_coq <- translateLocalIdent n
     withUsedCoqIdent n_coq $ f n_coq

-- | Invalidate all shared subterms that are not closed in a translation
invalidateOpenSharing :: TermTranslationMonad m => m a -> m a
invalidateOpenSharing =
  localTR (over sharedNames $ IntMap.filter sharedNameIsClosed)

-- | Run a translation in a context with one more SAW core variable with the
-- given name. Pass the corresponding Coq identifier used for this SAW core
-- variable to the computation in which it is bound.
withSAWVar :: TermTranslationMonad m => VarName -> (Coq.Ident -> m a) -> m a
withSAWVar n m =
  withFreshIdent (vnName n) $ \n_coq ->
  localTR (over namedEnvironment (Map.insert n n_coq)) $ m n_coq

-- | Find a fresh name generated from 'nextSharedName' to use in place of the
-- supplied 'Term' with the supplied index, and associate that index with the
-- fresh name in the 'sharedNames' sharing map. Pass the name that was generated
-- to the computation.
withSharedTerm :: TermTranslationMonad m => TermIndex -> Term ->
                  (Coq.Ident -> m a) -> m a
withSharedTerm idx t f =
  do ident <- (view nextSharedName <$> askTR) >>= freshVariant
     let sh_nm = SharedName ident $ closedTerm t
     localTR (set nextSharedName (nextVariant ident) .
              over sharedNames (IntMap.insert idx sh_nm)) $
       withUsedCoqIdent ident $ f ident

-- | Use 'withSharedTerm' to mark a list of terms as being shared
withSharedTerms :: TermTranslationMonad m => [(TermIndex,Term)] ->
                   ([Coq.Ident] -> m a) -> m a
withSharedTerms [] f = f []
withSharedTerms ((idx,t):ts) f =
  withSharedTerm idx t $ \n -> withSharedTerms ts $ \ns -> f (n:ns)


-- | The set of reserved identifiers in Coq, obtained from section
-- \"Gallina Specification Language\" of the Coq reference manual.
-- <https://coq.inria.fr/refman/language/gallina-specification-language.html>
reservedIdents :: Set Coq.Ident
reservedIdents =
  Set.fromList $
  map Coq.Ident $
  concatMap words $
  [ "_ Axiom CoFixpoint Definition Fixpoint Hypothesis IF Parameter Prop"
  , "SProp Set Theorem Type Variable as at by cofix discriminated else"
  , "end exists exists2 fix for forall fun if in lazymatch let match"
  , "multimatch return then using where with"
  ]

-- | Extract the list of names from a list of Coq declarations.  Not all
-- declarations have names, e.g. comments and code snippets come without names.
namedDecls :: [Coq.Decl] -> [Coq.Ident]
namedDecls = concatMap filterNamed
  where
    filterNamed :: Coq.Decl -> [Coq.Ident]
    filterNamed (Coq.Axiom n _)                               = [n]
    filterNamed (Coq.Parameter n _)                           = [n]
    filterNamed (Coq.Variable n _)                            = [n]
    filterNamed (Coq.Comment _)                               = []
    filterNamed (Coq.Definition n _ _ _)                      = [n]
    filterNamed (Coq.InductiveDecl (Coq.Inductive n _ _ _ _)) = [n]
    filterNamed (Coq.Snippet _)                               = []
    filterNamed (Coq.Section _ ds)                            = namedDecls ds

-- | Retrieve the names of all local and global declarations from the
-- translation state.
getNamesOfAllDeclarations ::
  TermTranslationMonad m =>
  m [Coq.Ident]
getNamesOfAllDeclarations = view allDeclarations <$> get
  where
    allDeclarations =
      to (\ (TranslationState {..}) -> namedDecls _topLevelDeclarations ++ _globalDeclarations)

-- | Run a term translation computation
runTermTranslationMonad ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  [Coq.Ident] ->
  [Coq.Ident] ->
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
      , _sawModuleMap       = mm })
  (TranslationState { _globalDeclarations = globalDecls
                    , _topLevelDeclarations  = []
                    })

-- | Return a Coq term for an error computation with the given string message
errorTermM :: TermTranslationMonad m => String -> m Coq.Term
errorTermM str = return $ Coq.App (Coq.Var "error") [Coq.StringLit str]

qualify :: ModuleName -> Coq.Ident -> Coq.Ident
qualify m (Coq.Ident i) = Coq.Ident (Text.unpack (moduleNameText m) ++ "." ++ i)

-- | Translate an 'Ident' with a given list of arguments to a Coq term, using
-- any special treatment for that identifier and qualifying it if necessary
translateIdentWithArgs :: TermTranslationMonad m => Ident -> [Term] -> m Coq.Term
translateIdentWithArgs i args = do
  currentModuleName <- asks (view currentModule . otherConfiguration)
  let identToCoq ident =
        if Just (identModule ident) == currentModuleName
          then base else qualify (translateModuleName (identModule ident)) base
        where
          base = escapeIdent (Coq.Ident (identName ident))
  specialTreatment <- findSpecialTreatment i
  applySpecialTreatment identToCoq (atUseSite specialTreatment)

  where

    applySpecialTreatment identToCoq UsePreserve =
      Coq.App (Coq.Var $ identToCoq i) <$> mapM translateTerm args
    applySpecialTreatment _identToCoq (UseRename targetModule targetName expl) =
      Coq.App
        ((if expl then Coq.ExplVar else Coq.Var) $
          qualify (fromMaybe (translateModuleName $ identModule i) targetModule)
          targetName)
          <$> mapM translateTerm args
    applySpecialTreatment _identToCoq (UseMacro n macroFun)
      | length args >= n
      , (m_args, args') <- splitAt n args =
        do f <- macroFun <$> mapM translateTerm m_args
           Coq.App f <$> mapM translateTerm args'
    applySpecialTreatment _identToCoq (UseMacro n _) =
      errorTermM (unwords
        [ "Identifier"
        , show i
        , "not applied to required number of args, which is"
        , show n
        ]
      )

-- | Helper for 'translateIdentWithArgs' with no arguments
translateIdent :: TermTranslationMonad m => Ident -> m Coq.Term
translateIdent i = translateIdentWithArgs i []

-- | Translate a constant to a Coq term. If the constant is named with
-- an 'Ident', then it already has a top-level translation from
-- translating the SAW core module containing that 'Ident'. If the
-- constant is an 'ImportedName', however, then it might not have a
-- Coq definition already, so add a definition of it to the top-level
-- translation state.
translateConstant :: TermTranslationMonad m => Name -> m Coq.Term
translateConstant nm
  | ModuleIdentifier ident <- nameInfo nm = translateIdent ident
translateConstant nm =
  do -- First, apply the constant renaming to get the name for this constant
     configuration <- asks translationConfiguration
     -- TODO short name seems wrong
     let nm_str = Text.unpack $ toShortName $ nameInfo nm
     let renamed =
           escapeIdent $ Coq.Ident $ fromMaybe nm_str $
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
         -- If not, add it as a Coq Variable declaration
         do tp <- withTopTranslationState $ translateTermLet (resolvedNameType resolved)
            modify (over topLevelDeclarations (Coq.Variable renamed tp :))

     -- Finally, return the constant as a Coq variable
     pure (Coq.Var renamed)


-- | Translate an 'Ident' and see if the result maps to a special 'Coq.Ident',
-- returning the latter 'Coq.Ident' if so
translateIdentToIdent :: TermTranslationMonad m => Ident -> m (Maybe Coq.Ident)
translateIdentToIdent i =
  (atUseSite <$> findSpecialTreatment i) >>= \case
    UsePreserve -> return $ Just (qualify translatedModuleName (Coq.Ident (Text.unpack (identBaseName i))))
    UseRename   targetModule targetName _ ->
      return $ Just $ qualify (fromMaybe translatedModuleName targetModule) targetName
    UseMacro _ _ -> return Nothing
  where
    translatedModuleName = translateModuleName (identModule i)

translateSort :: Sort -> Coq.Sort
translateSort s = if s == propSort then Coq.Prop else Coq.Type

flatTermFToExpr ::
  TermTranslationMonad m =>
  FlatTermF Term ->
  m Coq.Term
flatTermFToExpr tf = -- traceFTermF "flatTermFToExpr" tf $
  case tf of
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      ->
      -- We need to explicitly tell Coq that we want unit to be a Type, since
      -- all SAW core sorts are translated to Types
      pure (Coq.Ascription (Coq.Var "unit") (Coq.Sort Coq.Type))
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse translateTerm [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse translateTerm [x, y]
    PairLeft t    ->
      Coq.App <$> pure (Coq.Var "fst") <*> traverse translateTerm [t]
    PairRight t   ->
      Coq.App <$> pure (Coq.Var "snd") <*> traverse translateTerm [t]

    Recursor crec ->
      do let d = recursorDataType crec
         maybe_d_trans <-
           case nameInfo d of
             ModuleIdentifier ident -> translateIdentToIdent ident
             ImportedName{} -> pure Nothing
         case maybe_d_trans of
           Just (Coq.Ident i) -> return $ Coq.ExplVar (Coq.Ident (i ++ "_rect"))
           Nothing ->
             errorTermM ("Recursor for " ++ show d ++
                         " cannot be translated because the datatype " ++
                         "is mapped to an arbitrary Coq term")

    Sort s _h -> pure (Coq.Sort (translateSort s))
    NatLit i -> pure (Coq.NatLit (toInteger i))
    ArrayValue (asBoolType -> Just ()) (traverse asBool -> Just bits)
      | Pair w bv <- BV.bitsBE (Vector.toList bits)
      , Left LeqProof <- decideLeq (knownNat @1) w -> do
          return (Coq.App (Coq.Var "intToBv")
                  [Coq.NatLit (intValue w), Coq.ZLit (BV.asSigned w bv)])
    ArrayValue _ vec -> do
      elems <- Vector.toList <$> mapM translateTerm vec
      -- NOTE: with VectorNotations, this is actually a Coq vector literal
      return $ Coq.List elems
    StringLit s -> pure (Coq.Scope (Coq.StringLit (Text.unpack s)) "string")

    -- The translation of a record type {fld1:tp1, ..., fldn:tpn} is
    -- RecordTypeCons fld1 tp1 (... (RecordTypeCons fldn tpn RecordTypeNil)...).
    -- Note that SAW core equates record types up to reordering, so we sort our
    -- record types by field name to canonicalize them.
    RecordType fs ->
      foldr (\(name, tp) rest_m ->
              do rest <- rest_m
                 tp_trans <- translateTerm tp
                 return (Coq.App (Coq.Var "RecordTypeCons")
                         [Coq.StringLit (Text.unpack name), tp_trans, rest]))
      (return (Coq.Var "RecordTypeNil"))
      (sortOn fst fs)

    -- The translation of a record value {fld1 = x1, ..., fldn = xn} is
    -- RecordCons fld1 x1 (... (RecordCons fldn xn RecordNil) ...). Note that
    -- SAW core equates record values up to reordering, so we sort our record
    -- values by field name to canonicalize them.
    RecordValue fs ->
      foldr (\(name, trm) rest_m ->
              do rest <- rest_m
                 trm_trans <- translateTerm trm
                 return (Coq.App (Coq.Var "RecordCons")
                         [Coq.StringLit (Text.unpack name), trm_trans, rest]))
      (return (Coq.Var "RecordNil"))
      (sortOn fst fs)

    RecordProj r f -> do
      r_trans <- translateTerm r
      return (Coq.App (Coq.Var "RecordProj") [r_trans, Coq.StringLit (Text.unpack f)])

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
-- variables and no bound Coq identifiers
withTopTranslationState :: TermTranslationMonad m => m a -> m a
withTopTranslationState m =
  localTR (\r ->
            TranslationReader {
              _currentModule     = view currentModule r,
              _namedEnvironment  = Map.empty,
              _unavailableIdents = reservedIdents,
              _sharedNames       = IntMap.empty,
              _nextSharedName    = "var__0" ,
              _sawModuleMap      = view sawModuleMap r }) m

-- | Generate a Coq @Definition@ with a given name, body, and type, using the
-- lambda-bound variable names for the variables if they are available
mkDefinition :: Coq.Ident -> Coq.Term -> Coq.Term -> Coq.Decl
mkDefinition name (Coq.Lambda bs t) (Coq.Pi bs' tp)
  | length bs' == length bs =
    -- NOTE: there are a number of cases where length bs /= length bs', such as
    -- where the type of a definition is computed from some input (so might not
    -- have any explicit pi-abstractions), or where the body of a definition is
    -- a partially applied function (so might not have any lambdas). We could in
    -- theory try to handle these more complex cases by assigning names to some
    -- of the arguments, but it's not really necessary for the translation to be
    -- correct, so we just do the simple thing here.
    Coq.Definition name bs (Just tp) t
mkDefinition name t tp = Coq.Definition name [] (Just tp) t

mkLet :: (Coq.Ident, Coq.Term) -> Coq.Term -> Coq.Term
mkLet (name, rhs) body = Coq.Let name [] Nothing rhs body

-- | The result of translating a SAW core variable binding to Coq, including the
-- Coq identifier for the variable, the Coq translation of its type, and 0 or
-- more implicit Coq arguments that apply to the variable
data BindTrans = BindTrans { bindTransIdent :: Coq.Ident,
                             bindTransType :: Coq.Type,
                             bindTransImps :: [(Coq.Ident,Coq.Type)] }

-- | Convert a 'BindTrans' to a list of Coq term-level binders
bindTransToBinder :: BindTrans -> [Coq.Binder]
bindTransToBinder (BindTrans {..}) =
  Coq.Binder bindTransIdent (Just bindTransType) :
  map (\(n,ty) -> Coq.ImplicitBinder n (Just ty)) bindTransImps

-- | Convert a 'BindTrans' to a list of Coq type-level pi-abstraction binders
bindTransToPiBinder :: BindTrans -> [Coq.PiBinder]
bindTransToPiBinder (BindTrans { .. }) =
  case bindTransImps of
    [] | bindTransIdent == "_" -> [Coq.PiBinder Nothing bindTransType]
    [] -> [Coq.PiBinder (Just bindTransIdent) bindTransType]
    _ ->
      Coq.PiBinder (Just bindTransIdent) bindTransType :
      map (\(n,ty) -> Coq.PiImplicitBinder (Just n) ty) bindTransImps

-- | Given a 'VarName' and its type (as a 'Term'), translate the 'VarName'
-- to a Coq identifier, translate the type to a Coq term, and generate zero or
-- more additional 'Ident's and 'Type's representing additonal implicit
-- typeclass arguments, added if the given type is @isort@, etc. Pass all of
-- this information to the supplied computation, in which the SAW core variable
-- is bound to its Coq identifier.
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
           do nhty <- translateImplicitHyp (Coq.Var tc) args (Coq.Var n')
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

-- | Given a typeclass (as a Coq term), a list of 'LocalName's and their
-- corresponding types (as 'Term's), and a type-level function with argument
-- types given by the prior list, return a 'Pi' of the given arguments, inside
-- of which is an 'App' of the typeclass to the fully-applied type-level
-- function
translateImplicitHyp ::
  TermTranslationMonad m =>
  Coq.Term -> [(VarName, Term)] -> Coq.Term -> m Coq.Term
translateImplicitHyp tc [] tm = return (Coq.App tc [tm])
translateImplicitHyp tc args tm =
  translateBinders args $ \args' ->
  return $ Coq.Pi (concatMap mkPi args') (Coq.App tc [Coq.App tm (map mkArg args')])
  where
    mkPi (BindTrans nm ty nhs) =
      Coq.PiBinder (Just nm) ty :
      map (\(nh,nhty) -> Coq.PiImplicitBinder (Just nh) nhty) nhs
    mkArg b = Coq.Var $ bindTransIdent b

-- | Given a list of 'LocalName's and their corresponding types (as 'Term's),
-- return a list of explicit 'Binder's, for use representing the bound variables
-- in 'Lambda's, 'Let's, etc.
translateParams :: TermTranslationMonad m => [(VarName, Term)] ->
                   ([Coq.Binder] -> m a) -> m a
translateParams bs m =
  translateBinders bs (m . concat . map bindTransToBinder)

-- | Given a list of 'VarName's and their corresponding types (as 'Term's)
-- representing argument types and a 'Term' representing the return type,
-- return the resulting 'Pi', with additional implicit arguments added after
-- each instance of @isort@, @qsort@, etc.
translatePi :: TermTranslationMonad m => [(VarName, Term)] -> Term -> m Coq.Term
translatePi binders body =
  translatePiBinders binders $ \bindersT ->
  do bodyT <- translateTermLet body
     return $ Coq.Pi bindersT bodyT

-- | Given a 'LocalName' and its type (as a 'Term'), return an explicit
-- 'PiBinder' followed by zero or more implicit 'PiBinder's representing
-- additonal implicit typeclass arguments, added if the given type is @isort@,
-- @qsort@, etc.
translatePiBinders :: TermTranslationMonad m => [(VarName, Term)] ->
                      ([Coq.PiBinder] -> m a) -> m a
translatePiBinders bs m =
  translateBinders bs (m . concat . map bindTransToPiBinder)

-- | Find all subterms of a SAW core term that should be shared, and generate
-- let-bindings in Coq to bind them to local variables. Translate SAW core term
-- using those let-bindings for the shared subterms.
translateTermLet :: TermTranslationMonad m => Term -> m Coq.Term
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

-- | Translate a SAW core 'Term' to Coq, using let-bound Coq names when they are
-- associated with the given term for sharing
translateTerm :: TermTranslationMonad m => Term -> m Coq.Term
translateTerm t =
  case t of
    STApp { stAppIndex = i } ->
      do shared <- view sharedNames <$> askTR
         case IntMap.lookup i shared of
           Nothing -> translateTermUnshared t
           Just sh -> pure (Coq.Var $ sharedNameIdent sh)

-- | Translate a SAW core 'Term' to Coq without using sharing
translateTermUnshared :: TermTranslationMonad m => Term -> m Coq.Term
translateTermUnshared t =
  -- traceTerm "translateTerm" t $
  case unwrapTermF t of

    FTermF ftf -> flatTermFToExpr ftf

    Pi {} ->
      let (params, e) = asPiList t in
      translatePi params e

    Lambda {} ->
      let (params, e) = asLambdaList t in
      translateParams params $ \paramTerms ->
        do e' <- translateTermLet e
           return (Coq.Lambda paramTerms e')

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
            Coq.NatLit n' -> pure $ Coq.ZLit n'
            _ -> translateIdentWithArgs "Prelude.natToInt" [n]
          _ -> badTerm
        "Prelude.intNeg" ->
          case args of
          [z] -> translateTerm z >>= \case
            Coq.ZLit z' -> pure $ Coq.ZLit (-z')
            _ -> translateIdentWithArgs "Prelude.intNeg" [z]
          _ -> badTerm
        "Prelude.ite" ->
          case args of
          -- `rest` can be non-empty in examples like:
          -- (if b then f else g) arg1 arg2
          _ty : c : tt : ft : rest -> do
            ite <- Coq.If <$> translateTerm c <*> translateTerm tt <*> translateTerm ft
            case rest of
              [] -> return ite
              _  -> Coq.App ite <$> mapM translateTerm rest
          _ -> badTerm

        -- Refuse to translate any recursive value defined using Prelude.fix
        "Prelude.fix" -> badTerm

        _ -> translateIdentWithArgs i args
      _ -> Coq.App <$> translateTerm f <*> traverse translateTerm args

    -- Constants
    Constant n -> translateConstant n

    Variable nm _tp ->
      do nenv <- view namedEnvironment <$> askTR
         case Map.lookup nm nenv of
           Just ident -> pure (Coq.Var ident)
           Nothing ->
             do let nm_str = Text.unpack $ vnName nm
                let ident = escapeIdent $ Coq.Ident $ nm_str
                pure (Coq.Var ident)

  where
    badTerm          = Except.throwError $ BadTerm t

-- | In order to turn fixpoint computations into iterative computations, we need
-- to be able to create \"dummy\" values at the type of the computation.
defaultTermForType ::
  TermTranslationMonad m =>
  Term -> m Coq.Term
defaultTermForType typ = do
  case typ of
    (asBoolType -> Just ()) -> translateIdent (mkIdent preludeName "False")

    (isGlobalDef "Prelude.Nat" -> Just ()) -> return $ Coq.NatLit 0

    (asIntegerType -> Just ()) -> return $ Coq.ZLit 0

    (asSeq -> Just (n, typ')) -> do
      seqConst <- translateIdent (mkIdent (mkModuleName ["Cryptol"]) "seqConst")
      nT       <- translateTerm n
      typ'T    <- translateTerm typ'
      defaultT <- defaultTermForType typ'
      return $ Coq.App seqConst [ nT, typ'T, defaultT ]

    (asPairType -> Just (x,y)) -> do
      x' <- defaultTermForType x
      y' <- defaultTermForType y
      return $ Coq.App (Coq.Var "pair") [x',y']

    (asPiList -> (bs,body))
      | not (null bs)
      , closedTerm body ->
      do bs'   <- forM bs $ \ (_nm, ty) -> Coq.Binder "_" . Just <$> translateTerm ty
         body' <- defaultTermForType body
         return $ Coq.Lambda bs' body'

    _ -> Except.throwError $ CannotCreateDefaultValue typ

-- | Translate a SAW core term along with its type to a Coq term and its Coq
-- type, and pass the results to the supplied function
translateTermToDocWith ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  [Coq.Ident] -> -- ^ globals that have already been translated
  [Coq.Ident] -> -- ^ names of local variables in scope
  (Coq.Term -> Coq.Term -> Doc ann) ->
  Term -> Term ->
  Either (TranslationError Term) (Doc ann)
translateTermToDocWith configuration r mm globalDecls localEnv f t tp_trm = do
  ((term, tp), state) <-
    runTermTranslationMonad configuration r mm globalDecls localEnv
    ((,) <$> translateTermLet t <*> translateTermLet tp_trm)
  let decls = view topLevelDeclarations state
  return $
    vcat $
    [ (vcat . intersperse hardline . map Coq.ppDecl . reverse) decls
    , if null decls then mempty else hardline
    , f term tp
    ]

-- | Translate a SAW core 'Term' and its type (given as a 'Term') to a Coq
-- definition with the supplied name
translateDefDoc ::
  TranslationConfiguration ->
  Maybe ModuleName ->
  ModuleMap ->
  [Coq.Ident] ->
  Coq.Ident -> Term -> Term ->
  Either (TranslationError Term) (Doc ann)
translateDefDoc configuration r mm globalDecls name =
  translateTermToDocWith configuration r mm globalDecls [name]
  (\ t tp -> Coq.ppDecl $ mkDefinition name t tp)
