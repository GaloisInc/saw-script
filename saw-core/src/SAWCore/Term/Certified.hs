{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : SAWCore.Term.Certified
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.Term.Certified
  ( SharedContext -- abstract
  , Term -- abstract
  , TermIndex
  , unwrapTermF
  , termIndex
  , varTypes
  , freeVars
  , closedTerm
  , termSortOrType
  , alphaEquiv
    -- * Building certified terms
  , scTermF
  , scFlatTermF
  , scApply
  , scLambda
  , scLambdaList
  , scPi
  , scPiList
  , scFun
  , scFunAll
  , scConstant
  , scConst
  , scConstApply
  , scGlobal
  , scGlobalDef
  , scGlobalApply
  , scVariable
  , scVariables
  , scUnitValue
  , scUnitType
  , scPairValue
  , scPairType
  , scPairLeft
  , scPairRight
  , scRecursor
  , scRecordType
  , scRecordValue
  , scRecord
  , scRecordProj
  , scRecordSelect
  , scSort
  , scSortWithFlags
  , scNat
  , scVector
  , scString, scStringType
    -- * Typing and reduction
  , scTypeOf
  , scWhnf
  , scConvertibleEval
  , scConvertible
  , scSubtype
  , scInstantiate
  , scInstantiateBeta
  , scApplyAllBeta
  -- * SharedContext operations
  , mkSharedContext
  , scGetModuleMap
  , scGetNamingEnv
  , scRegisterName
  , scFreshVarName
  , scInjectCode
  , scDeclarePrim
  , scFreshConstant
  , scDefineConstant
  , scOpaqueConstant
  , scBeginDataType
  , scCompleteDataType
  , scImportModule
  , scLoadModule
  , scFreshName
  , scFreshenGlobalIdent
  , scResolveNameByURI
  , SharedContextCheckpoint
  , checkpointSharedContext
  , restoreSharedContext
    -- * Prettyprinting hooks (re-exported from SharedTerm; get them from
    -- there unless you need to be here for some reason)
  , prettyTerm
  , ppTerm
  ) where

import Control.Applicative
-- ((<$>), pure, (<*>))
import Control.Exception
import Control.Lens
import Control.Monad (foldM, forM, forM_, join, unless, when)

import Data.Bits
import qualified Data.Foldable as Fold
import Data.Foldable (foldlM, foldrM)
import Data.Hashable (Hashable(hash))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import qualified Data.IntSet as IntSet
import Data.IORef (IORef,newIORef,readIORef,modifyIORef',atomicModifyIORef',writeIORef)
import Data.List (find)
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import Numeric.Natural (Natural)
import Prelude hiding (maximum)
import Text.URI

import SAWSupport.IntRangeSet (IntRangeSet)
import qualified SAWSupport.IntRangeSet as IntRangeSet
import qualified SAWSupport.Pretty as PPS

import SAWCore.Cache
import SAWCore.Module
  ( beginDataType
  , completeDataType
  , dtName
  , ctorNumParams
  , ctorName
  , emptyModuleMap
  , moduleIsLoaded
  , moduleName
  , loadModule
  , lookupVarIndexInMap
  , insDefInMap
  , insInjectCodeInMap
  , insImportInMap
  , resolvedNameType
  , requireNameInMap
  , CtorArg(..)
  , CtorArgStruct(..)
  , Ctor(..)
  , DefQualifier(..)
  , DataType(..)
  , Def(..)
  , Module
  , ModuleMap
  , ResolvedName(..)
  )
import SAWCore.Name
import SAWCore.Panic (panic)
import SAWCore.Prelude.Constants
import SAWCore.Recognizer
import SAWCore.Term.Functor
import SAWCore.Term.Pretty
import SAWCore.Term.Raw
import SAWCore.Unique

scGlobal :: SharedContext -> Ident -> IO Term
scGlobal sc ident = scGlobalDef sc ident

-- possible errors: constant not defined
scConstant :: SharedContext -> Name -> IO Term
scConstant = scConst

-- possible errors: duplicate field name
scRecordValue :: SharedContext -> [(FieldName, Term)] -> IO Term
scRecordValue sc fields = scRecord sc (Map.fromList fields)

-- possible errors: not a record type, field name not found
scRecordProj :: SharedContext -> Term -> FieldName -> IO Term
scRecordProj sc t fname = scRecordSelect sc t fname


----------------------------------------------------------------------
-- Printing

-- Ideally these would be able to live in Pretty.hs, but they can't
-- because they need the `SharedContext`. They used to live in
-- SharedTerm.hs, but we would like to use them from inside here for
-- error reporting.

-- | The preferred printing mechanism for `Term`, if you want a `Doc`.
--
--   Note that there are two naming conventions in conflict here: the
--   convention that things using the `SharedContext` and in `IO`
--   should be named `sc`, and the convention that the preferred way
--   to prettyprint an object of type @Foo@ to a `Doc` should be
--   called @prettyFoo@. For the time being at least we've concluded
--   that the latter is more important.
prettyTerm :: SharedContext -> PPS.Opts -> Term -> IO PPS.Doc
prettyTerm sc opts t =
  do env <- scGetNamingEnv sc
     pure (prettyTermWithEnv opts env t)

-- | The preferred printing mechanism for `Term`, if you want text.
--
--   The same naming considerations as `prettyTerm` apply.
ppTerm :: SharedContext -> PPS.Opts -> Term -> IO String
ppTerm sc opts t =
  PPS.render opts <$> prettyTerm sc opts t


----------------------------------------------------------------------
-- TermFMaps

{-

Hash-consing story:

For scApply, we do a hash-consing lookup in 'appMapTFM' *before*
computing the result type (because computing the type may be expensive
in some cases). Terms in 'appMapTFM' must have the default type that
would normally be computed by scApply.

If we don't find the pair of keys in 'appMapTFM', only then do we
compute the result type, generate a new TermIndex, create a Term, and
then add it to appMapTFM.

For anything other than Apply nodes, we compute the type first.
(For non-Apply this should usually be fairly cheap to compute.)
Then we look up the pair of TermF and type together in hashMapTFM.

Terms may have types ascribed to them that are convertible (but not
equal) to the type that would have been computed by the typing rules.
When constructing an application term with a possibly-modified type,
we should do the following:

* Look up the TermF and type in hashMapTFM; if an entry is found,
  return it.

* Look up the two subterms in appMapTFM; if an entry is found *and the
  type matches*, then return it.

* If an entry with the wrong type was found in appMapTFM, then obtain
  a new TermIndex, add a new entry to hashMapTFM, and return the new
  term.

* If no entry was found in either table, we *could* compute the
  expected type for scApply and compare it to the given type to see
  which table the new term should go in. This is probably a very
  uncommon case.

In any case, a type-ascription operation should test for whether the
new type is identical to the old type and return the original term if
so.

-}

-- | A TermFMap is a data structure used for hash-consing of terms.
data TermFMap a
  = TermFMap
  { appMapTFM :: !(IntMap (IntMap a))
  , hashMapTFM :: !(HashMap (TermF Term, Either Sort Term) a)
  }

emptyTFM :: TermFMap a
emptyTFM = TermFMap mempty mempty

lookupAppTFM :: Term -> Term -> TermFMap a -> Maybe a
lookupAppTFM STApp{stAppIndex = i} STApp{stAppIndex = j} tfm =
  IntMap.lookup i (appMapTFM tfm) >>= IntMap.lookup j

insertAppTFM :: Term -> Term -> a -> TermFMap a -> TermFMap a
insertAppTFM STApp{stAppIndex = i} STApp{stAppIndex = j} x tfm =
  let f Nothing = Just (IntMap.singleton j x)
      f (Just m) = Just (IntMap.insert j x m)
  in tfm { appMapTFM = IntMap.alter f i (appMapTFM tfm) }

lookupTFM :: TermF Term -> Either Sort Term -> TermFMap a -> Maybe a
lookupTFM tf mty tfm =
  HMap.lookup (tf, mty) (hashMapTFM tfm)

insertTFM :: TermF Term -> Either Sort Term -> a -> TermFMap a -> TermFMap a
insertTFM tf mty x tfm =
  tfm { hashMapTFM = HMap.insert (tf, mty) x (hashMapTFM tfm) }

filterTFM :: (a -> Bool) -> TermFMap a -> TermFMap a
filterTFM p tfm =
  TermFMap
  { appMapTFM = IntMap.map (IntMap.filter p) (appMapTFM tfm)
  , hashMapTFM = HMap.filter p (hashMapTFM tfm)
  }

type AppCache = TermFMap Term

type AppCacheRef = IORef AppCache

emptyAppCache :: AppCache
emptyAppCache = emptyTFM

----------------------------------------------------------------------
-- SharedContext: a high-level interface for building Terms.

-- | 'SharedContext' is an abstract datatype representing all the
-- information necessary to resolve names and to construct,
-- type-check, normalize, and evaluate SAWCore 'Term's.
-- A 'SharedContext' contains mutable references so that it can be
-- extended at run-time with new names and declarations.

-- Invariant: scGlobalEnv is a cache with one entry for every global
-- declaration in 'scModuleMap' whose name is a 'ModuleIdentifier'.
-- Each map entry points to a 'Constant' term with the same 'Ident'.
-- It exists only to save one map lookup when building terms: Without
-- it we would first have to look up the Ident by URI in scURIEnv, and
-- then do another lookup for hash-consing the Constant term.
-- Invariant: All entries in 'scAppCache' must have 'TermIndex'es that
-- are less than 'scNextTermIndex' and marked valid in 'scValidTerms'.
data SharedContext = SharedContext
  { scModuleMap      :: IORef ModuleMap
  , scAppCache       :: AppCacheRef
  , scDisplayNameEnv :: IORef DisplayNameEnv
  , scURIEnv         :: IORef (Map URI VarIndex)
  , scGlobalEnv      :: IORef (HashMap Ident Term)
  , scNextVarIndex   :: IORef VarIndex
  , scNextTermIndex  :: IORef TermIndex
  , scValidTerms     :: IORef IntRangeSet
  }

-- | Internal function to get the next available 'TermIndex'. Not exported.
scFreshTermIndex :: SharedContext -> IO VarIndex
scFreshTermIndex sc = atomicModifyIORef' (scNextTermIndex sc) (\i -> (i + 1, i))

scEnsureValidTerm :: SharedContext -> Term -> IO ()
scEnsureValidTerm sc t =
  do s <- readIORef (scValidTerms sc)
     unless (IntRangeSet.member (termIndex t) s) $ do
       -- XXX: we should probably have the prettyprinting options in the SharedContext
       t' <- ppTerm sc PPS.defaultOpts t
       fail $ unlines $ [
           "Stale term encountered: index = " ++ show (termIndex t),
           "Valid indexes: " ++ show (IntRangeSet.toList s),
           t'
        ]

-- | Internal function to make a 'Term' from a 'TermF' with a given
-- variable typing context and type.
-- Precondition: The 'Either' argument should never have 'Right'
-- applied to a 'Sort'.
-- Precondition: All subterms should have been checked with 'scEnsureValidTerm'.
scMakeTerm :: SharedContext -> IntMap Term -> TermF Term -> Either Sort Term -> IO Term
scMakeTerm sc vt tf mty =
  do s <- readIORef (scAppCache sc)
     case lookupTFM tf mty s of
       Just term -> pure term
       Nothing ->
         do i <- scFreshTermIndex sc
            let term = STApp { stAppIndex = i
                             , stAppHash = hash tf
                             , stAppVarTypes = vt
                             , stAppTermF = tf
                             , stAppType = mty
                             }
            modifyIORef' (scAppCache sc) (insertTFM tf mty term)
            pure term

--------------------------------------------------------------------------------

data SharedContextCheckpoint =
  SCC
  { sccModuleMap :: ModuleMap
  , sccNamingEnv :: DisplayNameEnv
  , sccURIEnv    :: Map URI VarIndex
  , sccGlobalEnv :: HashMap Ident Term
  , sccTermIndex :: TermIndex
  }

checkpointSharedContext :: SharedContext -> IO SharedContextCheckpoint
checkpointSharedContext sc =
  do mmap <- readIORef (scModuleMap sc)
     nenv <- readIORef (scDisplayNameEnv sc)
     uenv <- readIORef (scURIEnv sc)
     genv <- readIORef (scGlobalEnv sc)
     i <- readIORef (scNextTermIndex sc)
     return SCC
            { sccModuleMap = mmap
            , sccNamingEnv = nenv
            , sccURIEnv = uenv
            , sccGlobalEnv = genv
            , sccTermIndex = i
            }

restoreSharedContext :: SharedContextCheckpoint -> SharedContext -> IO SharedContext
restoreSharedContext scc sc =
  do -- Ensure that the checkpoint itself is not stale
     let i = sccTermIndex scc
     s <- readIORef (scValidTerms sc)
     unless (IntRangeSet.member i s) $
       fail $ unlines $
       [ "Stale checkpoint encountered: index = " ++ show i
       , "Valid indexes: " ++ show (IntRangeSet.toList s)
       ]
     -- Restore saved environments
     writeIORef (scModuleMap sc) (sccModuleMap scc)
     writeIORef (scDisplayNameEnv sc) (sccNamingEnv scc)
     writeIORef (scURIEnv sc) (sccURIEnv scc)
     writeIORef (scGlobalEnv sc) (sccGlobalEnv scc)
     -- Mark 'TermIndex'es created since the checkpoint as invalid
     j <- readIORef (scNextTermIndex sc)
     modifyIORef' (scValidTerms sc) (IntRangeSet.delete (i, j-1))
     -- Filter stale terms from AppCache
     modifyIORef' (scAppCache sc) (filterTFM (\t -> termIndex t < i))
     -- scNextVarIndex and scNextTermIndex are left untouched
     pure sc

--------------------------------------------------------------------------------
-- Fundamental term builders

-- | Build a new 'Term' value from the given 'TermF'.
-- Reuse a 'Term' from the cache if an identical one already exists.
scTermF :: SharedContext -> TermF Term -> IO Term
scTermF sc tf =
  case tf of
    FTermF ftf -> scFlatTermF sc ftf
    App t1 t2 -> scApply sc t1 t2
    Lambda x t1 t2 -> scLambda sc x t1 t2
    Pi x t1 t2 -> scPi sc x t1 t2
    Constant nm -> scConst sc nm
    Variable x t1 -> scVariable sc x t1

-- | Create a new term from a lower-level 'FlatTermF' term.
scFlatTermF :: SharedContext -> FlatTermF Term -> IO Term
scFlatTermF sc ftf =
  case ftf of
    UnitValue -> scUnitValue sc
    UnitType -> scUnitType sc
    PairValue t1 t2 -> scPairValue sc t1 t2
    PairType t1 t2 -> scPairType sc t1 t2
    PairLeft t -> scPairLeft sc t
    PairRight t -> scPairRight sc t
    Recursor crec -> scRecursor sc (recursorDataType crec) (recursorSort crec)
    RecordType fs -> scRecordType sc fs
    RecordValue fs -> scRecord sc (Map.fromList fs)
    RecordProj t fname -> scRecordSelect sc t fname
    Sort s flags -> scSortWithFlags sc s flags
    ArrayValue t ts -> scVector sc t (V.toList ts)
    StringLit s -> scString sc s

-- | Create a function application term.
scApply ::
  SharedContext ->
  Term {- ^ The function to apply -} ->
  Term {- ^ The argument to apply to -} ->
  IO Term
scApply sc t1 t2 =
  -- Look up this application in the hash table first; if it is
  -- already there we can avoid recomputing the result type.
  do tfm <- readIORef (scAppCache sc)
     case lookupAppTFM t1 t2 tfm of
       Just term -> pure term
       Nothing ->
         do scEnsureValidTerm sc t1
            scEnsureValidTerm sc t2
            vt <- unifyVarTypes "scApply" sc (varTypes t1) (varTypes t2)
            ty1 <- scTypeOf sc t1
            (x, ty1a, ty1b) <- ensurePi sc ty1
            ty2 <- scTypeOf sc t2
            ok <- scSubtype sc ty2 ty1a
            unless ok $ do
              -- XXX we should probably have the prettyprint options in the SharedContext
              ty1a' <- ppTerm sc PPS.defaultOpts ty1a
              ty2' <- ppTerm sc PPS.defaultOpts ty2
              fail $ unlines $ [
                  "Not a subtype",
                  "expected: " ++ ty1a',
                  "got: " ++ ty2'
               ]
            -- Computing the result type with scInstantiateBeta may
            -- lead to other calls to scApply, but these should be at
            -- simpler types, so it should always terminate.
            ty <- scInstantiateBeta sc (IntMap.singleton (vnIndex x) t2) ty1b
            let mty = maybe (Right ty) Left (asSort ty)
            i <- scFreshTermIndex sc
            let tf = App t1 t2
            let term =
                  STApp
                  { stAppIndex = i
                  , stAppHash = hash tf
                  , stAppVarTypes = vt
                  , stAppTermF = tf
                  , stAppType = mty
                  }
            modifyIORef' (scAppCache sc) (insertAppTFM t1 t2 term)
            pure term

-- | Create a lambda term from a parameter name (as a 'VarName'),
-- parameter type (as a 'Term'), and a body ('Term').
-- All free variables with the same 'VarName' in the body become
-- bound.
scLambda ::
  SharedContext ->
  VarName {- ^ The parameter name -} ->
  Term {- ^ The parameter type -} ->
  Term {- ^ The body -} ->
  IO Term
scLambda sc x t body =
  do scEnsureValidTerm sc t
     scEnsureValidTerm sc body
     ensureNotFreeInContext x body
     _ <- unifyVarTypes "scLambda" sc (IntMap.singleton (vnIndex x) t) (varTypes body)
     vt <- unifyVarTypes "scLambda" sc (varTypes t) (IntMap.delete (vnIndex x) (varTypes body))
     rty <- scTypeOf sc body
     ty <- scPi sc x t rty
     scMakeTerm sc vt (Lambda x t body) (Right ty)

-- | Create a (possibly dependent) function given a parameter name,
-- parameter type (as a 'Term'), and a body ('Term').
-- All free variables with the same 'VarName' in the body become
-- bound.
scPi ::
  SharedContext ->
  VarName {- ^ The parameter name -} ->
  Term {- ^ The parameter type -} ->
  Term {- ^ The body -} ->
  IO Term
scPi sc x t body =
  do scEnsureValidTerm sc t
     scEnsureValidTerm sc body
     ensureNotFreeInContext x body
     _ <- unifyVarTypes "scPi" sc (IntMap.singleton (vnIndex x) t) (varTypes body)
     vt <- unifyVarTypes "scPi" sc (varTypes t) (IntMap.delete (vnIndex x) (varTypes body))
     s1 <- either pure (ensureSort sc) (stAppType t)
     s2 <- either pure (ensureSort sc) (stAppType body)
     scMakeTerm sc vt (Pi x t body) (Left (piSort s1 s2))

-- | Create a constant 'Term' from a 'Name'.
scConst :: SharedContext -> Name -> IO Term
scConst sc nm =
  do ty <- scTypeOfName sc nm
     let mty = maybe (Right ty) Left (asSort ty)
     scMakeTerm sc IntMap.empty (Constant nm) mty

-- | Create a named variable 'Term' from a 'VarName' and a type.
scVariable :: SharedContext -> VarName -> Term -> IO Term
scVariable sc x t =
  do scEnsureValidTerm sc t
     vt <- unifyVarTypes "scVariable" sc (IntMap.singleton (vnIndex x) t) (varTypes t)
     _s <- either pure (ensureSort sc) (stAppType t)
     let mty = maybe (Right t) Left (asSort t)
     scMakeTerm sc vt (Variable x t) mty

-- | Check whether the given 'VarName' occurs free in the type of
-- another variable in the context of the given 'Term', and fail if it
-- does.
ensureNotFreeInContext :: VarName -> Term -> IO ()
ensureNotFreeInContext x body =
  when (any (IntMap.member (vnIndex x) . varTypes) (varTypes body)) $
    fail $ "Variable occurs free in typing context: " ++ show (vnName x)

-- | Two typing contexts are unifiable if they agree perfectly on all
-- entries where they overlap.
unifyVarTypes :: String -> SharedContext -> IntMap Term -> IntMap Term -> IO (IntMap Term)
unifyVarTypes msg sc ctx1 ctx2 =
  do let check i t1 t2 =
           unless (t1 == t2) $ do
               t1' <- ppTerm sc PPS.defaultOpts t1
               t2' <- ppTerm sc PPS.defaultOpts t2
               fail $ unlines [
                   msg ++ ": variable typing context mismatch",
                   "VarIndex: " ++ show i,
                   "t1: " ++ t1',
                   "t2: " ++ t2'
                ]
     sequence_ (IntMap.intersectionWithKey check ctx1 ctx2)
     pure (IntMap.union ctx1 ctx2)

ensureRecognizer :: String -> SharedContext -> (Term -> Maybe a) -> Term -> IO a
ensureRecognizer s sc f trm =
  case f trm of
    Just a -> pure a
    Nothing ->
      do trm' <- scWhnf sc trm
         case f trm' of
           Just a -> pure a
           Nothing -> do
             trm'' <- ppTerm sc PPS.defaultOpts trm'
             fail $ "ensureRecognizer: Expected " ++ s ++ ", found: " ++ trm''

ensureSort :: SharedContext -> Term -> IO Sort
ensureSort sc tp = ensureRecognizer "Sort" sc asSort tp

ensurePi :: SharedContext -> Term -> IO (VarName, Term, Term)
ensurePi sc tp = ensureRecognizer "Pi" sc asPi tp

ensurePairType :: SharedContext -> Term -> IO (Term, Term)
ensurePairType sc tp = ensureRecognizer "PairType" sc asPairType tp

ensureRecordType :: SharedContext -> Term -> IO (Map FieldName Term)
ensureRecordType sc tp = ensureRecognizer "RecordType" sc asRecordType tp

piSort :: Sort -> Sort -> Sort
piSort s1 s2 = if s2 == propSort then propSort else max s1 s2

--------------------------------------------------------------------------------

-- | Create a function application term from the 'Name' of a global
-- constant and a list of 'Term' arguments.
scConstApply :: SharedContext -> Name -> [Term] -> IO Term
scConstApply sc i ts =
  do c <- scConst sc i
     scApplyAll sc c ts

-- | Create a list of named variables from a list of names and types.
scVariables :: Traversable t => SharedContext -> t (VarName, Term) -> IO (t Term)
scVariables sc = traverse (\(v, t) -> scVariable sc v t)

data DuplicateNameException = DuplicateNameException URI
instance Exception DuplicateNameException
instance Show DuplicateNameException where
  show (DuplicateNameException uri) =
      "Attempted to register the following name twice: " ++ Text.unpack (render uri)

-- | Internal function to get the next available 'VarIndex'. Not exported.
scFreshVarIndex :: SharedContext -> IO VarIndex
scFreshVarIndex sc = atomicModifyIORef' (scNextVarIndex sc) (\i -> (i + 1, i))

-- | Internal function to register a name with a caller-provided
-- 'VarIndex'. Not exported.
scRegisterNameWithIndex :: SharedContext -> VarIndex -> NameInfo -> IO ()
scRegisterNameWithIndex sc i nmi =
  do uris <- readIORef (scURIEnv sc)
     let uri = nameURI nmi
     when (Map.member uri uris) $ throwIO (DuplicateNameException uri)
     writeIORef (scURIEnv sc) (Map.insert uri i uris)
     modifyIORef' (scDisplayNameEnv sc) $ extendDisplayNameEnv i (nameAliases nmi)


-- | Generate a 'Name' with a fresh 'VarIndex' for the given
-- 'NameInfo' and register everything together in the naming
-- environment of the 'SharedContext'.
-- Throws 'DuplicateNameException' if the URI in the 'NameInfo' is
-- already registered.
scRegisterName :: SharedContext -> NameInfo -> IO Name
scRegisterName sc nmi =
  do i <- scFreshVarIndex sc
     scRegisterNameWithIndex sc i nmi
     pure (Name i nmi)

scResolveNameByURI :: SharedContext -> URI -> IO (Maybe VarIndex)
scResolveNameByURI sc uri =
  do env <- readIORef (scURIEnv sc)
     pure $! Map.lookup uri env

-- | Create a unique global name with the given base name.
scFreshName :: SharedContext -> Text -> IO Name
scFreshName sc x =
  do i <- scFreshVarIndex sc
     let uri = scFreshNameURI x i
     let nmi = ImportedName uri [x, x <> "#" <>  Text.pack (show i)]
     scRegisterNameWithIndex sc i nmi
     pure (Name i nmi)

-- | Create a 'VarName' with the given identifier (which may be "_").
scFreshVarName :: SharedContext -> Text -> IO VarName
scFreshVarName sc x = VarName <$> scFreshVarIndex sc <*> pure x

-- | Returns shared term associated with ident.
-- Does not check module namespace.
scGlobalDef :: SharedContext -> Ident -> IO Term
scGlobalDef sc ident =
  do m <- readIORef (scGlobalEnv sc)
     case HMap.lookup ident m of
       Nothing -> fail ("Could not find global: " ++ show ident)
       Just t -> pure t

-- | Internal function to register an 'Ident' with a 'Term' (which
-- must be a 'Constant' term with the same 'Ident') in the
-- 'scGlobalEnv' map of the 'SharedContext'. Not exported.
scRegisterGlobal :: SharedContext -> Ident -> Term -> IO ()
scRegisterGlobal sc ident t =
  do dup <- atomicModifyIORef' (scGlobalEnv sc) f
     when dup $ fail ("Global identifier already registered: " ++ show ident)
  where
    f m =
      case HMap.lookup ident m of
        Just _ -> (m, True)
        Nothing -> (HMap.insert ident t m, False)

-- | Find a variant of an identifier that is not already being used as a global,
-- by possibly adding a numeric suffix
scFreshenGlobalIdent :: SharedContext -> Ident -> IO Ident
scFreshenGlobalIdent sc ident =
  readIORef (scGlobalEnv sc) >>= \gmap ->
  return $ fromJust $ find (\i -> not $ HMap.member i gmap) $
  ident : map (mkIdent (identModule ident) .
               Text.append (identBaseName ident) .
               Text.pack . show) [(0::Integer) ..]

-- | Get the current naming environment
scGetNamingEnv :: SharedContext -> IO DisplayNameEnv
scGetNamingEnv sc = readIORef (scDisplayNameEnv sc)

-- | Get the current 'ModuleMap'
scGetModuleMap :: SharedContext -> IO ModuleMap
scGetModuleMap sc = readIORef (scModuleMap sc)

-- | Test if a module is loaded in the current shared context
scModuleIsLoaded :: SharedContext -> ModuleName -> IO Bool
scModuleIsLoaded sc name =
  moduleIsLoaded name <$> scGetModuleMap sc

-- | Load a module into the current shared context, raising an error if a module
-- of the same name is already loaded
scLoadModule :: SharedContext -> Module -> IO ()
scLoadModule sc m =
  do loaded <- scModuleIsLoaded sc (moduleName m)
     when loaded $ fail $ "scLoadModule: module "
                   ++ show (moduleName m) ++ " already loaded!"
     modifyIORef' (scModuleMap sc) (loadModule m)

-- | Bring a subset of names from one module into scope in a second module.
scImportModule ::
  SharedContext ->
  (Text -> Bool) {- ^ which names to import -} ->
  ModuleName {- ^ from this module -} ->
  ModuleName {- ^ into this module -} ->
  IO ()
scImportModule sc p mn1 mn2 =
  modifyIORef' (scModuleMap sc) (insImportInMap p mn1 mn2)

-- | Internal function to insert a definition into the 'ModuleMap' of
-- the 'SharedContext'. Throws 'DuplicateNameException' if the name is
-- already registered.
scInsDefInMap :: SharedContext -> Def -> IO ()
scInsDefInMap sc d =
  do e <- atomicModifyIORef' (scModuleMap sc) $ \mm ->
       case insDefInMap d mm of
         Left i -> (mm, Just (DuplicateNameException (moduleIdentToURI i)))
         Right mm' -> (mm', Nothing)
     maybe (pure ()) throwIO e

-- | Internal function to extend the SAWCore global environment with a
-- new constant, which may or may not have a definition. Not exported.
-- Assumes that the type and body (if present) are closed terms, and
-- that the body has the given type.
scDeclareDef ::
  SharedContext -> Name -> DefQualifier -> Term -> Maybe Term -> IO Term
scDeclareDef sc nm q ty body =
  do scInsDefInMap sc $
       Def
       { defName = nm
       , defQualifier = q
       , defType = ty
       , defBody = body
       }
     t <- scConst sc nm
     -- Register constant in scGlobalEnv if it has an Ident name
     case nameInfo nm of
       ModuleIdentifier ident -> scRegisterGlobal sc ident t
       ImportedName{} -> pure ()
     pure t

-- | Declare a SAW core primitive of the specified type.
scDeclarePrim :: SharedContext -> Ident -> DefQualifier -> Term -> IO ()
scDeclarePrim sc ident q def_tp =
  do let nmi = ModuleIdentifier ident
     nm <- scRegisterName sc nmi
     _ <- scDeclareDef sc nm q def_tp Nothing
     pure ()

-- Internal function
scFindDefBody :: SharedContext -> VarIndex -> IO (Maybe Term)
scFindDefBody sc vi =
  do mm <- scGetModuleMap sc
     case lookupVarIndexInMap vi mm of
       Just (ResolvedDef d) -> pure (defBody d)
       _ -> pure Nothing

-- | Insert an \"incomplete\" datatype, used as part of building up a
-- 'DataType' to typecheck its constructors. The constructors must be
-- registered separately with 'scCompleteDataType'.
scBeginDataType ::
  SharedContext ->
  Ident {- ^ The name of this datatype -} ->
  [(VarName, Term)] {- ^ The context of parameters of this datatype -} ->
  [(VarName, Term)] {- ^ The context of indices of this datatype -} ->
  Sort {- ^ The universe of this datatype -} ->
  IO Name
scBeginDataType sc dtIdent dtParams dtIndices dtSort =
  do dtName <- scRegisterName sc (ModuleIdentifier dtIdent)
     dtType <- scPiList sc (dtParams ++ dtIndices) =<< scSort sc dtSort
     dtMotiveName <- scFreshVarName sc "p"
     dtArgName <- scFreshVarName sc "arg"
     let dt = DataType { dtCtors = [], .. }
     e <- atomicModifyIORef' (scModuleMap sc) $ \mm ->
       case beginDataType dt mm of
         Left i -> (mm, Just (DuplicateNameException (moduleIdentToURI i)))
         Right mm' -> (mm', Nothing)
     maybe (pure ()) throwIO e
     scRegisterGlobal sc dtIdent =<< scConst sc dtName
     pure dtName

-- | Complete a datatype, by adding its constructors. See also 'scBeginDataType'.
scCompleteDataType :: SharedContext -> Ident -> [Ctor] -> IO ()
scCompleteDataType sc dtIdent ctors =
  do e <- atomicModifyIORef' (scModuleMap sc) $ \mm ->
       case completeDataType dtIdent ctors mm of
         Left i -> (mm, Just (DuplicateNameException (moduleIdentToURI i)))
         Right mm' -> (mm', Nothing)
     maybe (pure ()) throwIO e
     forM_ ctors $ \ctor ->
       case nameInfo (ctorName ctor) of
         ModuleIdentifier ident ->
           -- register constructor in scGlobalEnv if it has an Ident name
           scRegisterGlobal sc ident =<< scConst sc (ctorName ctor)
         ImportedName{} ->
           pure ()

-- | Insert an \"injectCode\" declaration to the given SAWCore module.
-- This declaration has no logical effect within SAW; it is used to
-- add extra code (like class instance declarations, for example) to
-- exported SAWCore modules in certain translation backends.
scInjectCode ::
  SharedContext ->
  ModuleName ->
  Text {- ^ Code namespace -} ->
  Text {- ^ Code to inject -} ->
  IO ()
scInjectCode sc mnm ns txt =
  modifyIORef' (scModuleMap sc) $ insInjectCodeInMap mnm ns txt

--------------------------------------------------------------------------------
-- Recursors

scRecursor :: SharedContext -> Name -> Sort -> IO Term
scRecursor sc nm s =
  do mm <- scGetModuleMap sc
     case lookupVarIndexInMap (nameIndex nm) mm of
       Just (ResolvedDataType dt) ->
         do unless (allowedElimSort dt s) $ fail "Disallowed propositional elimination"
            let d = dtName dt
            let nparams = length (dtParams dt)
            let nixs = length (dtIndices dt)
            let ctorOrder = map ctorName (dtCtors dt)
            let crec = CompiledRecursor d s nparams nixs ctorOrder
            let vt = IntMap.empty
            let tf = FTermF (Recursor crec)
            ty <- scRecursorType sc dt s
            scMakeTerm sc vt tf (Right ty)
       _ ->
         fail "datatype not found"

-- | Test whether a 'DataType' can be eliminated to the given sort. The rules
-- are that you can only eliminate propositional datatypes to the proposition
-- sort, unless your propositional data type is the empty type. This differs
-- slightly from the Coq rules, which allow elimination of propositional
-- datatypes with a single constructor that has only propositional arguments,
-- but this Coq behavior can be simulated with the behavior we are using here.
allowedElimSort :: DataType -> Sort -> Bool
allowedElimSort dt s =
  if dtSort dt == propSort && s /= propSort then
    length (dtCtors dt) == 1
  else True

-- | Compute the type of an eliminator function for a constructor from the name
-- of its datatype, its name, and its 'CtorArgStruct'. This type has, as free
-- variables, both the parameters of the datatype and a "motive" function from
-- indices of the datatype to a return type. It is of the form
--
-- > (x1::arg1) -> maybe (rec1::rec_tp1) -> .. ->
-- > (xn::argn) -> maybe (recn::rec_tpn) ->
-- >   p_ret ix_1 .. ix_k (ctor params x1 .. xn)
--
-- where the ixs are the type indices of the return type for the constructor,
-- the (xi::argi) are the arguments of the constructor, and the @maybe@s
-- indicate additional arguments that are present only for arguments of
-- recursive type, that is, where @argi@ has the form
--
-- > (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk
--
-- In this case, @rec_tpi@ has the form
--
-- > (z1::Z1) -> .. -> (zm::Zm) -> p_ret t1 .. tk (f z1 .. zm)
--
-- Note that the output type cannot be expressed in the type of this function,
-- since it depends on fields of the 'CtorArgStruct', so, instead, the result is
-- just casted to whatever type the caller specifies.
ctxCtorElimType ::
  SharedContext ->
  Name {- ^ data type name -} ->
  Name {- ^ constructor name -} ->
  Term {- ^ motive function -} ->
  CtorArgStruct ->
  IO Term
ctxCtorElimType sc d c p_ret (CtorArgStruct{..}) =
  do params <- scVariables sc ctorParams
     d_params <- scConstApply sc d params
     let helper :: [Term] -> [(VarName, CtorArg)] -> IO Term
         helper prevs ((nm, ConstArg tp) : args) =
           -- For a constant argument type, just abstract it and continue
           do arg <- scVariable sc nm tp
              rest <- helper (prevs ++ [arg]) args
              scPi sc nm tp rest
         helper prevs ((nm, RecursiveArg zs ts) : args) =
           -- For a recursive argument type of the form
           --
           -- (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk
           --
           -- form the type abstraction
           --
           -- (arg:: (z1::Z1) -> .. -> (zm::Zm) -> d params t1 .. tk) ->
           -- (ih :: (z1::Z1) -> .. -> (zm::Zm) -> p_ret t1 .. tk (arg z1 .. zm)) ->
           -- rest
           --
           -- where rest is the result of a recursive call
           do d_params_ts <- scApplyAll sc d_params ts
              -- Build the type of the argument arg
              arg_tp <- scPiList sc zs d_params_ts
              arg <- scVariable sc nm arg_tp
              -- Build the type of ih
              pret_ts <- scApplyAll sc p_ret ts
              z_vars <- scVariables sc zs
              arg_zs <- scApplyAll sc arg z_vars
              ih_ret <- scApply sc pret_ts arg_zs
              ih_tp <- scPiList sc zs ih_ret
              -- Finally, build the pi-abstraction for arg and ih around the rest
              rest <- helper (prevs ++ [arg]) args
              scPi sc nm arg_tp =<< scFun sc ih_tp rest
         helper prevs [] =
           -- If we are finished with our arguments, construct the final result type
           -- (p_ret ret_ixs (c params prevs))
           do p_ret_ixs <- scApplyAll sc p_ret ctorIndices
              appliedCtor <- scConstApply sc c (params ++ prevs)
              scApply sc p_ret_ixs appliedCtor
     helper [] ctorArgs

-- | Reduce an application of a recursor to a particular constructor.
-- This is known in the Coq literature as an iota reduction. More specifically,
-- the call
--
-- > ctxReduceRecursor rec f_c [x1, .., xk]
--
-- reduces the term @(RecursorApp rec ixs (CtorApp c ps xs))@ to
--
-- > f_c x1 (maybe rec_tm_1) .. xk (maybe rec_tm_k)
--
-- where @f_c@ is the eliminator function associated to the constructor @c@ by the
-- recursor value @rec@.  Here @maybe rec_tm_i@ indicates an optional recursive call
-- of the recursor on one of the @xi@. These recursive calls only exist for those
-- arguments @xi@ that are recursive arguments, i.e., that are specified with
-- 'RecursiveArg', and are omitted for non-recursive arguments specified by 'ConstArg'.
--
-- Specifically, for a @'RecursiveArg' zs ixs@ argument @xi@, which has type
-- @\(z1::Z1) -> .. -> d p1 .. pn ix1 .. ixp@, we build the recursive call
--
-- > \(z1::[xs/args]Z1) -> .. ->
-- >   RecursorApp rec [xs/args]ixs (xi z1 ... zn)
--
-- where @[xs/args]@ substitutes the concrete values for the earlier
-- constructor arguments @xs@ for the remaining free variables.

ctxReduceRecursor ::
  SharedContext ->
  Term {- ^ recursor applied to params, motive, and eliminator functions -} ->
  Term {- ^ constructor eliminator function -} ->
  [Term] {- ^ constructor arguments -} ->
  CtorArgStruct {- ^ constructor formal argument descriptor -} ->
  IO Term
ctxReduceRecursor sc r elimf c_args CtorArgStruct{..}
  | length c_args /= length ctorArgs = panic "ctxReduceRecursor" ["Wrong number of constructor arguments"]
  | otherwise =
    do args <- mk_args IntMap.empty (zip c_args ctorArgs)
       scWhnf sc =<< scApplyAll sc elimf args
  where
    mk_args :: IntMap Term ->  -- already processed parameters/arguments
               [(Term, (VarName, CtorArg))] ->
                 -- remaining actual arguments to process, with
                 -- telescope for typing the actual arguments
               IO [Term]
    -- no more arguments to process
    mk_args _ [] = return []

    -- process an argument that is not a recursive call
    mk_args pre_xs ((x, (nm, ConstArg _)) : xs_args) =
      do tl <- mk_args (IntMap.insert (vnIndex nm) x pre_xs) xs_args
         pure (x : tl)

    -- process an argument that is a recursive call
    mk_args pre_xs ((x, (nm, RecursiveArg zs ixs)) : xs_args) =
      do zs'  <- traverse (traverse (scInstantiate sc pre_xs)) zs
         ixs' <- traverse (scInstantiate sc pre_xs) ixs
         recx <- mk_rec_arg zs' ixs' x
         tl   <- mk_args (IntMap.insert (vnIndex nm) x pre_xs) xs_args
         pure (x : recx : tl)

    -- Build an individual recursive call, given the parameters, the bindings
    -- for the RecursiveArg, and the argument we are going to recurse on
    -- The resulting term has the form
    -- > \(z1:Z1) .. (zk:Zk) -> r ixs (x z1 .. zk)
    mk_rec_arg ::
      [(VarName, Term)] ->             -- telescope describing the zs
      [Term] ->                        -- actual values for the indices, shifted under zs
      Term ->                         -- actual value in recursive position
      IO Term
    mk_rec_arg zs_ctx ixs x =
      -- eta expand over the zs and apply the Recursor form
      do zs <- scVariables sc zs_ctx
         x_zs <- scApplyAll sc x zs
         r_ixs <- scApplyAll sc r ixs
         body <- scApply sc r_ixs x_zs
         scLambdaList sc zs_ctx body

-- | Build the type of the @p_ret@ function, also known as the "motive"
-- function, of a recursor on datatype @d@. This type has the form
--
-- > (i1::ix1) -> .. -> (im::ixm) -> d p1 .. pn i1 .. im -> s
--
-- where the @pi@ are the parameters of @d@, the @ixj@ are the indices
-- of @d@, and @s@ is any sort supplied as an argument.
-- Parameter variables @p1 .. pn@ will be free in the resulting term.
scRecursorMotiveType :: SharedContext -> DataType -> Sort -> IO Term
scRecursorMotiveType sc dt s =
  do param_vars <- scVariables sc (dtParams dt)
     ix_vars <- scVariables sc (dtIndices dt)
     d <- scConstApply sc (dtName dt) (param_vars ++ ix_vars)
     ret <- scFun sc d =<< scSort sc s
     scPiList sc (dtIndices dt) ret

-- | Build the type of a recursor for datatype @d@ that has been
-- applied to parameters, a motive function, and a full set of
-- eliminator functions. This type has the form
--
-- > (i1:ix1) -> .. -> (im:ixm) ->
-- >   (arg : d p1 .. pn i1 .. im) -> motive i1 .. im arg
--
-- where the @pi@ are the parameters of @d@, and the @ixj@ are the
-- indices of @d@.
-- Parameter variables @p1 .. pn@ will be free in the resulting term.
scRecursorAppType :: SharedContext -> DataType -> Term -> IO Term
scRecursorAppType sc dt motive =
  do param_vars <- scVariables sc (dtParams dt)
     ix_vars <- scVariables sc (dtIndices dt)
     d <- scConstApply sc (dtName dt) (param_vars ++ ix_vars)
     let arg_vn = dtArgName dt
     arg_var <- scVariable sc arg_vn d
     ret <- scApplyAll sc motive (ix_vars ++ [arg_var])
     scPiList sc (dtIndices dt ++ [(arg_vn, d)]) ret

-- | Build the full type of an unapplied recursor for datatype @d@
-- with elimination to sort @s@.
-- This type has the form
--
-- > (p1:pt1) -> .. -> (pn::ptn) ->
-- > (motive : (i1::ix1) -> .. -> (im::ixm) -> d p1 .. pn i1 .. im -> s) ->
-- > (elim1 : ..) -> .. (elimk : ..) ->
-- > (i1:ix1) -> .. -> (im:ixm) ->
-- >   (arg : d p1 .. pn i1 .. im) -> motive i1 .. im arg
scRecursorType :: SharedContext -> DataType -> Sort -> IO Term
scRecursorType sc dt s =
  do let d = dtName dt

     -- Compute the type of the motive function, which has the form
     -- (i1:ix1) -> .. -> (im:ixm) -> d p1 .. pn i1 .. im -> s
     motive_ty <- scRecursorMotiveType sc dt s
     let motive_vn = dtMotiveName dt
     motive_var <- scVariable sc motive_vn motive_ty

     -- Compute the types of the elimination functions
     elims_tps <-
       forM (dtCtors dt) $ \ctor ->
       ctxCtorElimType sc d (ctorName ctor) motive_var (ctorArgStruct ctor)

     scPiList sc (dtParams dt) =<<
       scPi sc motive_vn motive_ty =<<
       scFunAll sc elims_tps =<<
       scRecursorAppType sc dt motive_var

-- | Reduce an application of a recursor. This is known in the Coq literature as
-- an iota reduction. More specifically, the call
--
-- > scReduceRecursor sc rec crec ci [x1, .., xk]
--
-- reduces the term @(Recursor r elims ixs (CtorApp ci ps xs))@ to
--
-- > fi x1 (maybe rec_tm_1) .. xk (maybe rec_tm_k)
--
-- where @maybe rec_tm_i@ indicates an optional recursive call of the recursor
-- on one of the @xi@. These recursive calls only exist for those arguments
-- @xi@. See the documentation for 'ctxReduceRecursor' and the
-- 'ctorIotaReduction' field for more details.
scReduceRecursor ::
  SharedContext ->
  Term {- ^ recursor term -} ->
  CompiledRecursor {- ^ concrete data included in the recursor term -} ->
  [Term] {- ^ datatype parameters -} ->
  Term {- ^ motive function -} ->
  [Term] {- ^ eliminator functions -} ->
  Name {- ^ constructor name -} ->
  [Term] {- ^ constructor arguments -} ->
  IO Term
scReduceRecursor sc r crec params motive elims c args =
  do mres <- lookupVarIndexInMap (nameIndex c) <$> scGetModuleMap sc
     let cs_fs = Map.fromList (zip (map nameIndex (recursorCtorOrder crec)) elims)
     r_applied <- scApplyAll sc r (params ++ motive : elims)
     case mres of
       Just (ResolvedCtor ctor) ->
         -- The ctorIotaReduction field caches the result of iota reduction, which
         -- we just substitute into to perform the reduction
         ctorIotaReduction sc ctor r_applied cs_fs args
       _ ->
         panic "scReduceRecursor" ["Could not find constructor: " <> toAbsoluteName (nameInfo c)]

-- | Function for computing the result of one step of iota reduction
-- of the term
--
-- > dt#rec params elims ixs (c params args)
--
-- The arguments to this function are the recursor value (applied to
-- params, motive and elims), a mapping from constructor name indices
-- to eliminator functions, and the arguments to the constructor.
ctorIotaReduction ::
  SharedContext ->
  Ctor ->
  Term {- ^ recursor term -} ->
  Map VarIndex Term {- ^ constructor eliminators -} ->
  [Term] {- ^ constructor arguments -} ->
  IO Term
ctorIotaReduction sc ctor r cs_fs args =
  ctxReduceRecursor sc r elim args (ctorArgStruct ctor)
  where
    elim =
      case Map.lookup (nameIndex (ctorName ctor)) cs_fs of
        Just e -> e
        Nothing ->
          panic "ctorIotaReduction"
          ["no eliminator for constructor " <> toAbsoluteName (nameInfo (ctorName ctor))]

--------------------------------------------------------------------------------
-- Reduction to head-normal form

-- | An elimination for 'scWhnf'
data WHNFElim
  = ElimApp Term
  | ElimProj FieldName
  | ElimPair Bool
  | ElimRecursor Term CompiledRecursor [Term] Term [Term] [Term]
    -- ^ recursor, compiled recursor, params, motive, eliminators, indices

-- | Reduces beta-redexes, tuple/record selectors, recursor applications, and
-- definitions at the top level of a term.
scWhnf :: SharedContext -> Term -> IO Term
scWhnf sc t0 = go [] t0
  where
    go :: [WHNFElim] -> Term -> IO Term
    go xs                     (asApp            -> Just (t, x)) = go (ElimApp x : xs) t
    go xs                     (asRecordSelector -> Just (t, n)) = go (ElimProj n : xs) t
    go xs                     (asPairSelector -> Just (t, i))   = go (ElimPair i : xs) t
    go (ElimApp x : xs)       (asLambda -> Just (vn, _, body))  = betaReduce xs [(vn, x)] body
    go (ElimPair i : xs)      (asPairValue -> Just (a, b))      = go xs (if i then b else a)
    go (ElimProj fld : xs)    (asRecordValue -> Just elems)     = case Map.lookup fld elems of
                                                                    Just t -> go xs t
                                                                    Nothing ->
                                                                      error "scWhnf: field missing in record"
    go xs                     (asRecursorApp -> Just (r, crec)) | Just (params, ElimApp motive : xs1) <- splitApps (recursorNumParams crec) xs
                                                                , Just (elims, xs2) <- splitApps (length (recursorCtorOrder crec)) xs1
                                                                , Just (ixs, ElimApp x : xs') <- splitApps (recursorNumIxs crec) xs2
                                                                = go (ElimRecursor r crec params motive elims ixs : xs') x
    go xs                     t@(asConstant -> Just nm)         = do r <- resolveConstant nm
                                                                     case r of
                                                                       ResolvedDef d ->
                                                                         case defBody d of
                                                                           Just body -> go xs body
                                                                           Nothing -> foldM reapply t xs
                                                                       ResolvedCtor ctor ->
                                                                         case asArgsRec xs of
                                                                           Nothing -> foldM reapply t xs
                                                                           Just (rt, crec, params, motive, elims, args, xs') ->
                                                                             do let args' = drop (ctorNumParams ctor) args
                                                                                scReduceRecursor sc rt crec params motive elims nm args' >>= go xs'
                                                                       ResolvedDataType _ ->
                                                                         foldM reapply t xs

    go xs                     t                                 = foldM reapply t xs

    betaReduce :: [WHNFElim] -> [(VarName, Term)] -> Term -> IO Term
    betaReduce (ElimApp x : xs) vs (asLambda -> Just (vn,_,body)) =
      betaReduce xs ((vn, x) : vs) body
    betaReduce xs vs body =
      do let subst = IntMap.fromList [ (vnIndex vn, x) | (vn, x) <- vs ]
         body' <- scInstantiate sc subst body
         go xs body'

    reapply :: Term -> WHNFElim -> IO Term
    reapply t (ElimApp x) = scApply sc t x
    reapply t (ElimProj i) = scRecordSelect sc t i
    reapply t (ElimPair i) = scPairSelector sc t i
    reapply t (ElimRecursor r _crec params motive elims ixs) =
      do f <- scApplyAll sc r (params ++ motive : elims ++ ixs)
         scApply sc f t

    resolveConstant :: Name -> IO ResolvedName
    resolveConstant nm = requireNameInMap nm <$> scGetModuleMap sc

    -- look for a prefix of ElimApps followed by an ElimRecursor
    asArgsRec :: [WHNFElim] -> Maybe (Term, CompiledRecursor, [Term], Term, [Term], [Term], [WHNFElim])
    asArgsRec (ElimRecursor r crec params motive elims _ixs : xs) = Just (r, crec, params, motive, elims, [], xs)
    asArgsRec (ElimApp x : xs) =
      case asArgsRec xs of
        Just (r, crec, params, motive, elims, args, xs') -> Just (r, crec, params, motive, elims, x : args, xs')
        Nothing -> Nothing
    asArgsRec _ = Nothing

    -- look for a prefix of n ElimApps
    splitApps :: Int -> [WHNFElim] -> Maybe ([Term], [WHNFElim])
    splitApps 0 xs = Just ([], xs)
    splitApps n (ElimApp t : xs) =
       do (ts, xs') <- splitApps (n-1) xs
          Just (t : ts, xs')
    splitApps _ _ = Nothing


-- | Test if two terms are convertible up to a given evaluation procedure. In
-- practice, this procedure is usually 'scWhnf', possibly combined with some
-- rewriting.
scConvertibleEval :: SharedContext
                  -> (SharedContext -> Term -> IO Term)
                  -> Bool -- ^ Should constants be unfolded during this check?
                  -> Term
                  -> Term
                  -> IO Bool
scConvertibleEval sc eval unfoldConst tm1 tm2 = do
   c <- newCache
   go c IntMap.empty tm1 tm2

 where whnf :: Cache IO TermIndex Term -> Term -> IO (TermF Term)
       whnf c t@(STApp{ stAppIndex = idx}) =
         unwrapTermF <$> useCache c idx (eval sc t)

       go :: Cache IO TermIndex Term -> IntMap VarIndex -> Term -> Term -> IO Bool
       go _c vm (STApp{stAppIndex = idx1, stAppVarTypes = vt1}) (STApp{stAppIndex = idx2})
         | IntMap.disjoint vt1 vm && idx1 == idx2 = pure True   -- succeed early case
       go c vm t1 t2 = join (goF c vm <$> whnf c t1 <*> whnf c t2)

       goF :: Cache IO TermIndex Term -> IntMap VarIndex -> TermF Term -> TermF Term -> IO Bool

       goF _c _vm (Constant nx) (Constant ny) | nameIndex nx == nameIndex ny = pure True
       goF c vm (Constant nx) y
           | unfoldConst =
             do mx <- scFindDefBody sc (nameIndex nx)
                case mx of
                  Just x -> join (goF c vm <$> whnf c x <*> return y)
                  Nothing -> pure False
       goF c vm x (Constant ny)
           | unfoldConst =
             do my <- scFindDefBody sc (nameIndex ny)
                case my of
                  Just y -> join (goF c vm <$> return x <*> whnf c y)
                  Nothing -> pure False

       goF c vm (FTermF ftf1) (FTermF ftf2) =
               case zipWithFlatTermF (go c vm) ftf1 ftf2 of
                 Nothing -> return False
                 Just zipped -> Fold.and <$> traverse id zipped

       goF c vm (App f1 x1) (App f2 x2) =
              pure (&&) <*> go c vm f1 f2 <*> go c vm x1 x2

       goF c vm (Lambda (vnIndex -> i1) ty1 body1) (Lambda (vnIndex -> i2) ty2 body2) =
         pure (&&) <*> go c vm ty1 ty2 <*> go c vm' body1 body2
           where vm' = if i1 == i2 then vm else IntMap.insert i1 i2 vm

       goF c vm (Pi (vnIndex -> i1) ty1 body1) (Pi (vnIndex -> i2) ty2 body2) =
         pure (&&) <*> go c vm ty1 ty2 <*> go c vm' body1 body2
           where vm' = if i1 == i2 then vm else IntMap.insert i1 i2 vm

       goF c vm (Variable x1 t1) (Variable x2 t2)
         | i' == vnIndex x2 = go c vm t1 t2
           where i' = case IntMap.lookup (vnIndex x1) vm of
                        Nothing -> vnIndex x1
                        Just i -> i

       -- final catch-all case
       goF _c _vm _x _y = pure False

-- | Test if two terms are convertible using 'scWhnf' for evaluation
scConvertible :: SharedContext
              -> Bool -- ^ Should constants be unfolded during this check?
              -> Term
              -> Term
              -> IO Bool
scConvertible sc = scConvertibleEval sc scWhnf

-- | Check whether one type is a subtype of another: Either they are
-- convertible, or they are both Pi types with convertible argument
-- types and result sorts @s1@ and @s2@ with @s1 <= s2@.
scSubtype :: SharedContext -> Term -> Term -> IO Bool
scSubtype sc t1 t2
  | alphaEquiv t1 t2 = pure True
  | otherwise =
    do t1' <- scWhnf sc t1
       t2' <- scWhnf sc t2
       case (t1', t2') of
         (asSort -> Just s1, asSort -> Just s2) ->
           pure (s1 <= s2)
         (unwrapTermF -> Pi x1 a1 b1, unwrapTermF -> Pi x2 a2 b2)
           | x1 == x2 ->
             (&&) <$> scConvertible sc True a1 a2 <*> scSubtype sc b1 b2
           | otherwise ->
             do conv1 <- scConvertible sc True a1 a2
                var1 <- scVariable sc x1 a1
                b2' <- scInstantiate sc (IntMap.singleton (vnIndex x2) var1) b2
                conv2 <- scSubtype sc b1 b2'
                pure (conv1 && conv2)
         _ ->
           scConvertible sc True t1' t2'


--------------------------------------------------------------------------------
-- Type checking

-- | Look up the type of a global constant, given its 'Name'.
scTypeOfName :: SharedContext -> Name -> IO Term
scTypeOfName sc nm =
  do mm <- scGetModuleMap sc
     case lookupVarIndexInMap (nameIndex nm) mm of
       Just r -> pure (resolvedNameType r)
       Nothing -> fail ("scTypeOfName: Name not found: " ++ show nm)

-- | Return the type of a term.
scTypeOf :: SharedContext -> Term -> IO Term
scTypeOf sc t =
  case stAppType t of
    Right ty -> pure ty
    Left s -> scSort sc s

--------------------------------------------------------------------------------
-- Beta Normalization

-- | Instantiate some of the named variables in the term, reducing any
-- new beta redexes created in the process.
-- The substitution 'IntMap' is keyed by 'VarIndex'.
-- If the input term and all terms in the substitution are in
-- beta-normal form, then the result will also be beta-normal.
-- If a substituted term is a lambda, and it is substituted into the
-- left side of an application, creating a new beta redex, then it
-- will trigger further beta reduction.
-- Existing beta redexes in the input term or substitution are
-- not reduced.
scInstantiateBeta :: SharedContext -> IntMap Term -> Term -> IO Term
scInstantiateBeta sc sub t0 =
  do let domainVars = IntMap.keysSet sub
     let rangeVars = foldMap freeVars sub
     cache <- newCacheIntMap
     let memo :: Term -> IO Term
         memo t@STApp{stAppIndex = i} = useCache cache i (go t)
         go :: Term -> IO Term
         go t
           | IntSet.disjoint domainVars (freeVars t) = pure t
           | otherwise = goArgs t []
         goArgs :: Term -> [Term] -> IO Term
         goArgs t args =
           case unwrapTermF t of
             FTermF ftf ->
               do ftf' <- traverse memo ftf
                  t' <- scFlatTermF sc ftf'
                  scApplyAll sc t' args
             App t1 t2 ->
               do t2' <- memo t2
                  goArgs t1 (t2' : args)
             Lambda x t1 t2 ->
               do t1' <- memo t1
                  (x', t2') <- goBinder x t1' t2
                  t' <- scLambda sc x' t1' t2'
                  scApplyAll sc t' args
             Pi x t1 t2 ->
               do t1' <- memo t1
                  (x', t2') <- goBinder x t1' t2
                  t' <- scPi sc x' t1' t2'
                  scApplyAll sc t' args
             Constant {} ->
               scApplyAll sc t args
             Variable x t1 ->
               case IntMap.lookup (vnIndex x) sub of
                 Just t' -> scApplyAllBeta sc t' args
                 Nothing ->
                   do t1' <- memo t1
                      t' <- scVariable sc x t1'
                      scApplyAll sc t' args
         goBinder :: VarName -> Term -> Term -> IO (VarName, Term)
         goBinder x@(vnIndex -> i) t body
           | IntSet.member i rangeVars =
               -- Possibility of capture; rename bound variable.
               do x' <- scFreshVarName sc (vnName x)
                  var <- scVariable sc x' t
                  let sub' = IntMap.insert i var sub
                  body' <- scInstantiateBeta sc sub' body
                  pure (x', body')
           | IntMap.member i sub =
               -- Shadowing; remove entry from substitution.
               do let sub' = IntMap.delete i sub
                  body' <- scInstantiateBeta sc sub' body
                  pure (x, body')
           | otherwise =
               -- No possibility of shadowing or capture.
               do body' <- memo body
                  pure (x, body')
     go t0

-- | Apply a function 'Term' to a list of zero or more arguments.
-- If the function is a lambda term, then beta reduce the arguments
-- into the function body.
-- If all input terms are in beta-normal form, then the result will
-- also be beta-normal.
scApplyAllBeta :: SharedContext -> Term -> [Term] -> IO Term
scApplyAllBeta _ t0 [] = pure t0
scApplyAllBeta sc t0 (arg0 : args0) =
  case asLambda t0 of
    Nothing -> scApplyAll sc t0 (arg0 : args0)
    Just (x, _, body) -> go (IntMap.singleton (vnIndex x) arg0) body args0
  where
    go :: IntMap Term -> Term -> [Term] -> IO Term
    go sub (asLambda -> Just (x, _, body)) (arg : args) =
      go (IntMap.insert (vnIndex x) arg sub) body args
    go sub t args =
      do t' <- scInstantiateBeta sc sub t
         scApplyAllBeta sc t' args


--------------------------------------------------------------------------------
-- Building shared terms

-- | Apply a function 'Term' to zero or more argument 'Term's.
scApplyAll :: SharedContext -> Term -> [Term] -> IO Term
scApplyAll sc = foldlM (scApply sc)

-- | Create a term from a 'Sort'.
scSort :: SharedContext -> Sort -> IO Term
scSort sc s = scSortWithFlags sc s noFlags

-- | Create a term from a 'Sort', and set the given advisory flags
scSortWithFlags :: SharedContext -> Sort -> SortFlags -> IO Term
scSortWithFlags sc s flags =
  scMakeTerm sc IntMap.empty (FTermF (Sort s flags)) (Left (sortOf s))

-- | Create a literal term from a 'Natural'.
scNat :: SharedContext -> Natural -> IO Term
scNat sc 0 = scGlobalDef sc "Prelude.Zero"
scNat sc n =
  do p <- scPos sc n
     scGlobalApply sc "Prelude.NatPos" [p]

scPos :: SharedContext -> Natural -> IO Term
scPos sc n
  | n <= 1    = scGlobalDef sc "Prelude.One"
  | otherwise =
    do arg <- scPos sc (div n 2)
       let ident = if even n then "Prelude.Bit0" else "Prelude.Bit1"
       scGlobalApply sc ident [arg]

-- | Create a literal term (of saw-core type @String@) from a 'Text'.
scString :: SharedContext -> Text -> IO Term
scString sc s =
  do ty <- scStringType sc
     scMakeTerm sc IntMap.empty (FTermF (StringLit s)) (Right ty)

-- | Create a term representing the primitive saw-core type @String@.
scStringType :: SharedContext -> IO Term
scStringType sc = scGlobalDef sc preludeStringIdent

-- | Create a vector term from a type (as a 'Term') and a list of 'Term's of
-- that type.
scVector :: SharedContext -> Term -> [Term] -> IO Term
scVector sc e xs =
  do scEnsureValidTerm sc e
     vt <- foldM (unifyVarTypes "scVector" sc) (varTypes e) (map varTypes xs)
     let check x =
           do scEnsureValidTerm sc x
              xty <- scTypeOf sc x
              ok <- scSubtype sc xty e
              unless ok $ do
                  e' <- ppTerm sc PPS.defaultOpts e
                  xty' <- ppTerm sc PPS.defaultOpts xty
                  fail $ unlines [
                      "Not a subtype",
                      "expected: " ++ e',
                      "got: " ++ xty'
                   ]
     mapM_ check xs
     n <- scNat sc (fromIntegral (length xs))
     let tf = FTermF (ArrayValue e (V.fromList xs))
     ty <- scVecType sc n e
     scMakeTerm sc vt tf (Right ty)

-- | Create a term representing a vector type, from a term giving the length
-- and a term giving the element type.
scVecType :: SharedContext -> Term -> Term -> IO Term
scVecType sc n e = scGlobalApply sc preludeVecIdent [n, e]

-- | Create a record term from a 'Map' from 'FieldName's to 'Term's.
scRecord :: SharedContext -> Map FieldName Term -> IO Term
scRecord sc (Map.toList -> fields) =
  do mapM_ (scEnsureValidTerm sc . snd) fields
     vt <- foldM (unifyVarTypes "scRecord" sc) IntMap.empty (map (varTypes . snd) fields)
     let tf = FTermF (RecordValue fields)
     field_tys <- traverse (traverse (scTypeOf sc)) fields
     ty <- scRecordType sc field_tys
     scMakeTerm sc vt tf (Right ty)

-- | Create a record field access term from a 'Term' representing a record and
-- a 'FieldName'.
scRecordSelect :: SharedContext -> Term -> FieldName -> IO Term
scRecordSelect sc t fname =
  do scEnsureValidTerm sc t
     let vt = varTypes t
     let tf = FTermF (RecordProj t fname)
     field_tys <- ensureRecordType sc =<< scTypeOf sc t
     case Map.lookup fname field_tys of
       Nothing -> fail "scRecordSelect: field name not found"
       Just ty' -> scMakeTerm sc vt tf (Right ty')

-- | Create a term representing the type of a record from a list associating
-- field names (as 'FieldName's) and types (as 'Term's). Note that the order of
-- the given list is irrelevant, as record fields are not ordered.
scRecordType :: SharedContext -> [(FieldName, Term)] -> IO Term
scRecordType sc field_tys =
  do mapM_ (scEnsureValidTerm sc . snd) field_tys
     vt <- foldM (unifyVarTypes "scRecordType" sc) IntMap.empty (map (varTypes . snd) field_tys)
     let tf = FTermF (RecordType field_tys)
     let field_sort (_, t) = either pure (ensureSort sc) (stAppType t)
     sorts <- traverse field_sort field_tys
     let s = foldl max (mkSort 0) sorts
     scMakeTerm sc vt tf (Left s)

-- | Create a unit-valued term.
scUnitValue :: SharedContext -> IO Term
scUnitValue sc =
  do ty <- scUnitType sc
     scMakeTerm sc IntMap.empty (FTermF UnitValue) (Right ty)

-- | Create a term representing the unit type.
scUnitType :: SharedContext -> IO Term
scUnitType sc =
  scMakeTerm sc IntMap.empty (FTermF UnitType) (Left (TypeSort 0))

-- | Create a pair term from two terms.
scPairValue :: SharedContext
            -> Term -- ^ The left projection
            -> Term -- ^ The right projection
            -> IO Term
scPairValue sc t1 t2 =
  do scEnsureValidTerm sc t1
     scEnsureValidTerm sc t2
     vt <- unifyVarTypes "scPairValue" sc (varTypes t1) (varTypes t2)
     let tf = FTermF (PairValue t1 t2)
     ty1 <- scTypeOf sc t1
     ty2 <- scTypeOf sc t2
     ty <- scPairType sc ty1 ty2
     scMakeTerm sc vt tf (Right ty)

-- | Create a term representing a pair type from two other terms, each
-- representing a type.
scPairType :: SharedContext
           -> Term -- ^ Left projection type
           -> Term -- ^ Right projection type
           -> IO Term
scPairType sc t1 t2 =
  do scEnsureValidTerm sc t1
     scEnsureValidTerm sc t2
     vt <- unifyVarTypes "scPairType" sc (varTypes t1) (varTypes t2)
     let tf = FTermF (PairType t1 t2)
     s1 <- either pure (ensureSort sc) (stAppType t1)
     s2 <- either pure (ensureSort sc) (stAppType t2)
     scMakeTerm sc vt tf (Left (max s1 s2))

-- | Create a term giving the left projection of a 'Term' representing a pair.
scPairLeft :: SharedContext -> Term -> IO Term
scPairLeft sc t =
  do scEnsureValidTerm sc t
     (ty, _) <- ensurePairType sc =<< scTypeOf sc t
     let mty = maybe (Right ty) Left (asSort ty)
     scMakeTerm sc (varTypes t) (FTermF (PairLeft t)) mty

-- | Create a term giving the right projection of a 'Term' representing a pair.
scPairRight :: SharedContext -> Term -> IO Term
scPairRight sc t =
  do scEnsureValidTerm sc t
     (_, ty) <- ensurePairType sc =<< scTypeOf sc t
     let mty = maybe (Right ty) Left (asSort ty)
     scMakeTerm sc (varTypes t) (FTermF (PairRight t)) mty

-- | Create a term representing either the left or right projection of the
-- given 'Term', depending on the given 'Bool': left if @False@, right if @True@.
scPairSelector :: SharedContext -> Term -> Bool -> IO Term
scPairSelector sc t False = scPairLeft sc t
scPairSelector sc t True = scPairRight sc t

-- | Create a term representing the type of a non-dependent function, given a
-- parameter and result type (as 'Term's).
scFun :: SharedContext
      -> Term -- ^ The parameter type
      -> Term -- ^ The result type
      -> IO Term
scFun sc a b = scPi sc wildcardVarName a b

-- | Create a term representing the type of a non-dependent n-ary function,
-- given a list of parameter types and a result type (as terms).
scFunAll :: SharedContext
         -> [Term] -- ^ The parameter types
         -> Term   -- ^ The result type
         -> IO Term
scFunAll sc argTypes resultType = foldrM (scFun sc) resultType argTypes

-- | Create a lambda term of multiple arguments (curried) from a list
-- associating parameter names to types (as 'Term's) and a body.
-- The parameters are listed outermost first.
-- Variable names in the parameter list are in scope for all parameter
-- types occurring later in the list.
scLambdaList :: SharedContext
             -> [(VarName, Term)] -- ^ List of parameter / parameter type pairs
             -> Term -- ^ The body
             -> IO Term
scLambdaList _ [] rhs = return rhs
scLambdaList sc ((nm,tp):r) rhs =
  scLambda sc nm tp =<< scLambdaList sc r rhs

-- | Create a (possibly dependent) function of multiple arguments (curried)
-- from a list associating parameter names to types (as 'Term's) and a body.
-- Variable names in the parameter list are in scope for all parameter
-- types occurring later in the list.
scPiList :: SharedContext
         -> [(VarName, Term)] -- ^ List of parameter / parameter type pairs
         -> Term -- ^ The body
         -> IO Term
scPiList _ [] rhs = return rhs
scPiList sc ((nm,tp):r) rhs = scPi sc nm tp =<< scPiList sc r rhs

-- | Define a global constant with the specified base name (as
-- 'Text'), body, and type.
-- The term for the body must not have any free variables.
-- A globally-unique name with the specified base name will be created
-- using 'scFreshName'.
scFreshConstant ::
  SharedContext ->
  Text {- ^ The base name -} ->
  Term {- ^ The body -} ->
  Term {- ^ The type -} ->
  IO Term
scFreshConstant sc name rhs ty =
  do unless (closedTerm rhs) $ do
       ty' <- ppTerm sc PPS.defaultOpts ty
       rhs' <- ppTerm sc PPS.defaultOpts rhs
       fail $ unlines [
           "scFreshConstant: term contains free variables",
           "name: " ++ Text.unpack name,
           "ty: " ++ ty',
           "rhs: " ++ rhs'
        ]
     nm <- scFreshName sc name
     scDeclareDef sc nm NoQualifier ty (Just rhs)

-- | Define a global constant with the specified name (as 'NameInfo'),
-- body, and type.
-- The URI in the given 'NameInfo' must be globally unique.
-- The term for the body must not have any free variables.
scDefineConstant ::
  SharedContext ->
  NameInfo {- ^ The name -} ->
  Term {- ^ The body -} ->
  Term {- ^ The type -} ->
  IO Term
scDefineConstant sc nmi rhs ty =
  do unless (closedTerm rhs) $ do
       ty' <- ppTerm sc PPS.defaultOpts ty
       rhs' <- ppTerm sc PPS.defaultOpts rhs
       fail $ unlines [
           "scDefineConstant: term contains free variables",
           "nmi: " ++ Text.unpack (toAbsoluteName nmi),
           "ty: " ++ ty',
           "rhs: " ++ rhs'
        ]
     nm <- scRegisterName sc nmi
     scDeclareDef sc nm NoQualifier ty (Just rhs)


-- | Declare a global opaque constant with the specified name (as
-- 'NameInfo') and type.
-- Such a constant has no definition, but unlike a variable it may be
-- used in other constant definitions and is not subject to
-- lambda-binding or substitution.
scOpaqueConstant ::
  SharedContext ->
  NameInfo ->
  Term {- ^ type of the constant -} ->
  IO Term
scOpaqueConstant sc nmi ty =
  do nm <- scRegisterName sc nmi
     scDeclareDef sc nm NoQualifier ty Nothing

-- | Create a function application term from a global identifier and a list of
-- arguments (as 'Term's).
scGlobalApply :: SharedContext -> Ident -> [Term] -> IO Term
scGlobalApply sc i ts =
    do c <- scGlobalDef sc i
       scApplyAll sc c ts


------------------------------------------------------------

-- | The default instance of the SharedContext operations.
mkSharedContext :: IO SharedContext
mkSharedContext =
  do vr <- newIORef (1 :: VarIndex) -- 0 is reserved for wildcardVarName.
     cr <- newIORef emptyAppCache
     gr <- newIORef HMap.empty
     mr <- newIORef emptyModuleMap
     dr <- newIORef emptyDisplayNameEnv
     ur <- newIORef Map.empty
     -- The top 16 bits of the TermIndex form a unique ID for this
     -- particular SharedContext.
     -- We expect that the low 48 bits will never overflow.
     scid <- getUniqueInt
     let i0 = scid `shiftL` 48
     tr <- newIORef (i0 :: TermIndex)
     let j0 = i0 + (1 `shiftL` 48 - 1)
     ir <- newIORef (IntRangeSet.singleton (i0, j0))
     pure $
       SharedContext
       { scModuleMap = mr
       , scAppCache = cr
       , scNextVarIndex = vr
       , scDisplayNameEnv = dr
       , scURIEnv = ur
       , scGlobalEnv = gr
       , scNextTermIndex = tr
       , scValidTerms = ir
       }

-- | Instantiate some of the named variables in the term.
-- The 'IntMap' is keyed by 'VarIndex'.
-- Note: The replacement is _not_ applied recursively
-- to the terms in the substitution map.
scInstantiate :: SharedContext -> IntMap Term -> Term -> IO Term
scInstantiate sc vmap t0 =
  do let domainVars = IntMap.keysSet vmap
     let rangeVars = foldMap freeVars vmap
     tcache <- newCacheIntMap
     let memo :: Term -> IO Term
         memo t =
           case t of
             STApp {stAppIndex = i} -> useCache tcache i (go t)
         go :: Term -> IO Term
         go t
           | IntSet.disjoint domainVars (freeVars t) = pure t
           | otherwise =
             case unwrapTermF t of
               FTermF ftf     -> scFlatTermF sc =<< traverse memo ftf
               App t1 t2      -> scTermF sc =<< App <$> memo t1 <*> memo t2
               Lambda x t1 t2 ->
                 do t1' <- memo t1
                    (x', t2') <- goBinder x t1' t2
                    scLambda sc x' t1' t2'
               Pi x t1 t2 ->
                 do t1' <- memo t1
                    (x', t2') <- goBinder x t1' t2
                    scPi sc x' t1' t2'
               Constant {} -> pure t
               Variable nm tp ->
                 case IntMap.lookup (vnIndex nm) vmap of
                   Just t' -> pure t'
                   Nothing -> scVariable sc nm =<< memo tp
         goBinder :: VarName -> Term -> Term -> IO (VarName, Term)
         goBinder x@(vnIndex -> i) t body
           | IntSet.member i rangeVars =
               -- Possibility of capture; rename bound variable.
               do x' <- scFreshVarName sc (vnName x)
                  var <- scVariable sc x' t
                  let vmap' = IntMap.insert i var vmap
                  body' <- scInstantiate sc vmap' body
                  pure (x', body')
           | IntMap.member i vmap =
               -- Shadowing; remove entry from substitution.
               do let vmap' = IntMap.delete i vmap
                  body' <- scInstantiate sc vmap' body
                  pure (x, body')
           | otherwise =
               -- No possibility of shadowing or capture.
               do body' <- memo body
                  pure (x, body')
     go t0
