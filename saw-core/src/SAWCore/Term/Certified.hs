{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}

{- |
Module      : SAWCore.Term.Certified
Copyright   : Galois, Inc. 2025
License     : BSD3
Maintainer  : huffman@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module is the interface to the trusted kernel of SAWCore.
The API is built around operations in the SAWCore monad, 'SCM'.
Such functions are recognized by the @scm@ prefix.

The API guarantees that all 'Term's are well-formed and well-typed
with respect to the 'SharedContext' they were built with.
Attempting to build an invalid 'Term' will result in a failure of type
'TermError' being raised in the 'SCM' monad.
-}

module SAWCore.Term.Certified
  ( -- * Terms
    SharedContext -- abstract
  , Term -- abstract
  , TermIndex
  , unwrapTermF
  , termIndex
  , varTypes
  , freeVars
  , closedTerm
  , termSortOrType
  , alphaEquiv
    -- * Term building monad
  , TermError(..)
  , SCM
  , runSCM
    -- * Building certified terms
  , scmAscribe
  , scmTermF
  , scmFlatTermF
  , scmApply
  , scmLambda
  , scmPi
  , scmPiList
  , scmConst
  , scmGlobalDef
  , scmVariable
  , scmUnitValue
  , scmUnitType
  , scmPairValue
  , scmPairType
  , scmPairLeft
  , scmPairRight
  , scmRecursor
  , scmRecordType
  , scmRecordValue
  , scmRecordSelect
  , scmSort
  , scmSortWithFlags
  , scmNat
  , scmVector
  , scmString
    -- * Typing and reduction
  , scmTypeOf
  , scmEnsureSortType
  , scmWhnf
  , scmConvertible
  , scmSubtype
  , scmInstantiate
  , scmInstantiateBeta
  , scmApplyAllBeta
  , scmReduceRecursor
  -- * SharedContext operations
  , mkSharedContext
  , scGetModuleMap
  , scGetNamingEnv
  , scmRegisterName
  , scmFreshVarName
  , scInjectCode
  , scmDeclarePrim
  , scmFreshConstant
  , scmDefineConstant
  , scmOpaqueConstant
  , DataTypeSpec(..)
  , CtorSpec(..)
  , scmDefineDataType
  , scImportModule
  , scLoadModule
  , scmFreshName
  , scFreshenGlobalIdent
  , scResolveQualName
    -- * Checkpointing
  , SharedContextCheckpoint
  , checkpointSharedContext
  , restoreSharedContext
  ) where

import Control.Lens
import Control.Monad (foldM, forM, unless, when)
import Control.Monad.Except (ExceptT(..), runExceptT, throwError)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (ReaderT(..), runReaderT, ask)

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
import Data.Ref (C)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import Numeric.Natural (Natural)
import Prelude hiding (maximum)

import SAWSupport.IntRangeSet (IntRangeSet)
import qualified SAWSupport.IntRangeSet as IntRangeSet

import SAWCore.Cache
import SAWCore.Module
  ( dtName
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
  , insTypeDeclInMap
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
import SAWCore.Term.Raw
import SAWCore.Unique
import qualified SAWCore.QualName as QN

----------------------------------------------------------------------

-- | Errors that can occur while constructing 'Term's.
data TermError
  = StaleTerm Term IntRangeSet
  | VariableContextMismatch Text VarIndex Term Term
  | ApplyNotPiType Term Term -- function, argument
  | ApplyNotSubtype Term Term Term -- function, expected, arg
  | VariableFreeInContext VarName Term
  | NotType Term
  | NotPairType Term
  | NameNotFound Name
  | IdentNotFound Ident
  | NotRecord Term
  | FieldNotFound Term FieldName
  | VectorNotSubtype Term Term -- expected type, element
  | DataTypeNotFound Name
  | RecursorPropElim Name Sort
  | ConstantNotClosed Name Term
  | DuplicateQualName QN.QualName
  | AlreadyDefined Name
  | AscriptionNotSubtype Term Term -- expected type, body
  | DataTypeKindNotClosed Name Term
  | DataTypeParameterSort Name Sort VarName Term -- dt name, dt sort, param name, param type
  | DataTypeIndexSort Name Sort VarName Term -- dt name, dt sort, index name, index type
  | DataTypeCtorNotClosed Name Name Term -- dt name, ctor name, ctor type
  | DataTypeCtorSort Name Sort Name Term -- dt name, dt sort, ctor name, ctor type

----------------------------------------------------------------------
-- SAWCore Monad

newtype SCM a = SCM (ReaderT SharedContext (ExceptT TermError IO) a)
  deriving (Functor, Applicative, Monad, MonadIO, C)

scmSharedContext :: SCM SharedContext
scmSharedContext = SCM ask

scmError :: TermError -> SCM a
scmError err = SCM (throwError err)

runSCM :: SharedContext -> SCM a -> IO (Either TermError a)
runSCM sc (SCM m) = runExceptT (runReaderT m sc)

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
-- it we would first have to look up the Ident by QualName in scQualNameEnv, and
-- then do another lookup for hash-consing the Constant term.
-- Invariant: All entries in 'scAppCache' must have 'TermIndex'es that
-- are less than 'scNextTermIndex' and marked valid in 'scValidTerms'.
data SharedContext = SharedContext
  { scModuleMap      :: IORef ModuleMap
  , scAppCache       :: AppCacheRef
  , scDisplayNameEnv :: IORef DisplayNameEnv
  , scQualNameEnv    :: IORef (Map QN.QualName VarIndex)
  , scGlobalEnv      :: IORef (HashMap Ident Term)
  , scNextVarIndex   :: IORef VarIndex
  , scNextTermIndex  :: IORef TermIndex
  , scValidTerms     :: IORef IntRangeSet
  }

-- | Internal function to get the next available 'TermIndex'. Not exported.
scmFreshTermIndex :: SCM VarIndex
scmFreshTermIndex =
  do sc <- scmSharedContext
     liftIO $ atomicModifyIORef' (scNextTermIndex sc) (\i -> (i + 1, i))

-- | Check that the given 'Term' has not been invalidated by rolling
-- back to a saved checkpoint with 'restoreSharedContext'.
-- Otherwise raise a 'StaleTerm' error.
scmEnsureValidTerm :: Term -> SCM ()
scmEnsureValidTerm t =
  do sc <- scmSharedContext
     s <- liftIO $ readIORef (scValidTerms sc)
     unless (IntRangeSet.member (termIndex t) s) $ scmError (StaleTerm t s)

-- | Internal function to make a 'Term' from a 'TermF' with a given
-- variable typing context and type.
-- Precondition: The 'Either' argument should never have 'Right'
-- applied to a 'Sort'.
-- Precondition: All subterms should have been checked with
-- 'scmEnsureValidTerm'.
scmMakeTerm :: IntMap Term -> TermF Term -> Either Sort Term -> SCM Term
scmMakeTerm vt tf mty =
  do sc <- scmSharedContext
     s <- liftIO $ readIORef (scAppCache sc)
     case lookupTFM tf mty s of
       Just term -> pure term
       Nothing ->
         do i <- scmFreshTermIndex
            let term = STApp { stAppIndex = i
                             , stAppHash = hash tf
                             , stAppVarTypes = vt
                             , stAppTermF = tf
                             , stAppType = mty
                             }
            liftIO $ modifyIORef' (scAppCache sc) (insertTFM tf mty term)
            pure term

--------------------------------------------------------------------------------

data SharedContextCheckpoint =
  SCC
  { sccModuleMap :: ModuleMap
  , sccNamingEnv :: DisplayNameEnv
  , sccQualNameEnv :: Map QN.QualName VarIndex
  , sccGlobalEnv :: HashMap Ident Term
  , sccTermIndex :: TermIndex
  }

checkpointSharedContext :: SharedContext -> IO SharedContextCheckpoint
checkpointSharedContext sc =
  do mmap <- readIORef (scModuleMap sc)
     nenv <- readIORef (scDisplayNameEnv sc)
     uenv <- readIORef (scQualNameEnv sc)
     genv <- readIORef (scGlobalEnv sc)
     i <- readIORef (scNextTermIndex sc)
     return SCC
            { sccModuleMap = mmap
            , sccNamingEnv = nenv
            , sccQualNameEnv = uenv
            , sccGlobalEnv = genv
            , sccTermIndex = i
            }

restoreSharedContext :: SharedContextCheckpoint -> SharedContext -> IO ()
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
     writeIORef (scQualNameEnv sc) (sccQualNameEnv scc)
     writeIORef (scGlobalEnv sc) (sccGlobalEnv scc)
     -- Mark 'TermIndex'es created since the checkpoint as invalid
     j <- readIORef (scNextTermIndex sc)
     modifyIORef' (scValidTerms sc) (IntRangeSet.delete (i, j-1))
     -- Filter stale terms from AppCache
     modifyIORef' (scAppCache sc) (filterTFM (\t -> termIndex t < i))
     -- scNextVarIndex and scNextTermIndex are left untouched

--------------------------------------------------------------------------------
-- Fundamental term builders

-- | Build a variant of a 'Term' with a specific type.
-- The first term's type must be a subtype of the second term.
scmAscribe :: Term -> Term -> SCM Term
scmAscribe t0 ty =
  do let mty = maybe (Right ty) Left (asSort ty)
     ty0 <- scmTypeOf t0
     sc <- scmSharedContext
     ok <- scmSubtype ty0 ty
     unless ok $ scmError (AscriptionNotSubtype ty t0)
     let tf = unwrapTermF t0
     let fallback = scmMakeTerm (varTypes t0) tf mty
     tfm <- liftIO $ readIORef (scAppCache sc)
     case tf of
       App f arg ->
         case lookupAppTFM f arg tfm of
           Just t' ->
             if fmap termIndex mty == fmap termIndex (termSortOrType t')
             then pure t' else fallback
           Nothing -> fallback
       _ -> fallback

-- | Build a new 'Term' value from the given 'TermF'.
-- Reuse a 'Term' from the cache if an identical one already exists.
scmTermF :: TermF Term -> SCM Term
scmTermF tf =
  case tf of
    FTermF ftf -> scmFlatTermF ftf
    App t1 t2 -> scmApply t1 t2
    Lambda x t1 t2 -> scmLambda x t1 t2
    Pi x t1 t2 -> scmPi x t1 t2
    Constant nm -> scmConst nm
    Variable x t1 -> scmVariable x t1

-- | Create a new term from a lower-level 'FlatTermF' term.
scmFlatTermF :: FlatTermF Term -> SCM Term
scmFlatTermF ftf =
  case ftf of
    UnitValue -> scmUnitValue
    UnitType -> scmUnitType
    PairValue t1 t2 -> scmPairValue t1 t2
    PairType t1 t2 -> scmPairType t1 t2
    PairLeft t -> scmPairLeft t
    PairRight t -> scmPairRight t
    Recursor crec -> scmRecursor (recursorDataType crec) (recursorSort crec)
    Sort s flags -> scmSortWithFlags s flags
    ArrayValue t ts -> scmVector t (V.toList ts)
    StringLit s -> scmString s

-- | Create a function application term, or return a 'TermError'.
scmApply ::
  Term {- ^ The function to apply -} ->
  Term {- ^ The argument to apply to -} ->
  SCM Term
scmApply t1 t2 =
  -- Look up this application in the hash table first; if it is
  -- already there we can avoid recomputing the result type.
  do sc <- scmSharedContext
     tfm <- liftIO $ readIORef (scAppCache sc)
     case lookupAppTFM t1 t2 tfm of
       Just term -> pure term
       Nothing ->
         do scmEnsureValidTerm t1
            scmEnsureValidTerm t2
            vt <- scmUnifyVarTypes "scApply" (varTypes t1) (varTypes t2)
            ty1 <- scmTypeOf t1
            (x, ty1a, ty1b) <- scmEnsureRecognizer (ApplyNotPiType t1 t2) asPi ty1
            ty2 <- scmTypeOf t2
            ok <- scmSubtype ty2 ty1a
            unless ok $ scmError (ApplyNotSubtype t1 ty1a t2)
            -- Computing the result type with scmInstantiateBeta may
            -- lead to other calls to scApply, but these should be at
            -- simpler types, so it should always terminate.
            ty <- scmInstantiateBeta (IntMap.singleton (vnIndex x) t2) ty1b
            let mty = maybe (Right ty) Left (asSort ty)
            i <- scmFreshTermIndex
            let tf = App t1 t2
            let term =
                  STApp
                  { stAppIndex = i
                  , stAppHash = hash tf
                  , stAppVarTypes = vt
                  , stAppTermF = tf
                  , stAppType = mty
                  }
            liftIO $ modifyIORef' (scAppCache sc) (insertAppTFM t1 t2 term)
            pure term

-- | Create a lambda term from a parameter name (as a 'VarName'),
-- parameter type (as a 'Term'), and a body ('Term').
-- All free variables with the same 'VarName' in the body become
-- bound.
scmLambda ::
  VarName {- ^ The parameter name -} ->
  Term {- ^ The parameter type -} ->
  Term {- ^ The body -} ->
  SCM Term
scmLambda x t body =
  do scmEnsureValidTerm t
     scmEnsureValidTerm body
     scmEnsureNotFreeInContext x body
     _ <- scmUnifyVarTypes "scLambda" (IntMap.singleton (vnIndex x) t) (varTypes body)
     vt <- scmUnifyVarTypes "scLambda" (varTypes t) (IntMap.delete (vnIndex x) (varTypes body))
     rty <- scmTypeOf body
     ty <- scmPi x t rty
     scmMakeTerm vt (Lambda x t body) (Right ty)

-- | Create a (possibly dependent) function given a parameter name,
-- parameter type (as a 'Term'), and a body ('Term').
-- All free variables with the same 'VarName' in the body become
-- bound.
scmPi ::
  VarName {- ^ The parameter name -} ->
  Term {- ^ The parameter type -} ->
  Term {- ^ The body -} ->
  SCM Term
scmPi x t body =
  do scmEnsureValidTerm t
     scmEnsureValidTerm body
     scmEnsureNotFreeInContext x body
     _ <- scmUnifyVarTypes "scPi" (IntMap.singleton (vnIndex x) t) (varTypes body)
     vt <- scmUnifyVarTypes "scPi" (varTypes t) (IntMap.delete (vnIndex x) (varTypes body))
     s1 <- scmEnsureSortType t
     s2 <- scmEnsureSortType body
     scmMakeTerm vt (Pi x t body) (Left (piSort s1 s2))

-- | Create a constant 'Term' from a 'Name'.
scmConst :: Name -> SCM Term
scmConst nm =
  do ty <- scmTypeOfName nm
     let mty = maybe (Right ty) Left (asSort ty)
     scmMakeTerm IntMap.empty (Constant nm) mty

-- | Create a named variable 'Term' from a 'VarName' and a type.
scmVariable :: VarName -> Term -> SCM Term
scmVariable x t =
  do scmEnsureValidTerm t
     vt <- scmUnifyVarTypes "scVariable" (IntMap.singleton (vnIndex x) t) (varTypes t)
     _s <- scmEnsureSortType t
     let mty = maybe (Right t) Left (asSort t)
     scmMakeTerm vt (Variable x t) mty

-- | Check whether the given 'VarName' occurs free in the type of
-- another variable in the context of the given 'Term', and fail if it
-- does.
scmEnsureNotFreeInContext :: VarName -> Term -> SCM ()
scmEnsureNotFreeInContext x body =
  when (any (IntMap.member (vnIndex x) . varTypes) (varTypes body)) $
    scmError $ VariableFreeInContext x body

-- | Two typing contexts are unifiable if they agree perfectly on all
-- entries where they overlap.
scmUnifyVarTypes :: Text -> IntMap Term -> IntMap Term -> SCM (IntMap Term)
scmUnifyVarTypes msg ctx1 ctx2 =
  do let check i t1 t2 =
           unless (termIndex t1 == termIndex t2) $
           scmError (VariableContextMismatch msg i t1 t2)
     sequence_ (IntMap.intersectionWithKey check ctx1 ctx2)
     pure (IntMap.union ctx1 ctx2)

scmEnsureRecognizer :: TermError -> (Term -> Maybe a) -> Term -> SCM a
scmEnsureRecognizer err f trm =
  case f trm of
    Just a -> pure a
    Nothing ->
      do trm' <- scmWhnf trm
         case f trm' of
           Just a -> pure a
           Nothing -> scmError err

-- | Ensure the type of a 'Term' is a sort, and return that sort.
scmEnsureSortType :: Term -> SCM Sort
scmEnsureSortType t =
  case termSortOrType t of
    Left s -> pure s
    Right ty -> scmEnsureRecognizer (NotType t) asSort ty

scmEnsurePairType :: Term -> SCM (Term, Term)
scmEnsurePairType t =
  do ty <- scmTypeOf t
     scmEnsureRecognizer (NotPairType t) asPairType ty

piSort :: Sort -> Sort -> Sort
piSort s1 s2 = if s2 == propSort then propSort else max s1 s2

--------------------------------------------------------------------------------

-- | Create a function application term from the 'Name' of a global
-- constant and a list of 'Term' arguments.
scmConstApply :: Name -> [Term] -> SCM Term
scmConstApply i ts =
  do c <- scmConst i
     scmApplyAll c ts

-- | Create a list of named variables from a list of names and types.
scmVariables :: Traversable t => t (VarName, Term) -> SCM (t Term)
scmVariables = traverse (\(v, t) -> scmVariable v t)

-- | Internal function to get the next available 'VarIndex'. Not exported.
scmFreshVarIndex :: SCM VarIndex
scmFreshVarIndex =
  do sc <- scmSharedContext
     liftIO $ atomicModifyIORef' (scNextVarIndex sc) (\i -> (i + 1, i))

-- | Internal function to register a name with a caller-provided
-- 'VarIndex'. Not exported.
scmRegisterNameWithIndex :: VarIndex -> NameInfo -> SCM ()
scmRegisterNameWithIndex i nmi =
  do sc <- scmSharedContext
     qns <- liftIO $ readIORef (scQualNameEnv sc)
     let qn = toQualName nmi
     when (Map.member qn qns) $ scmError (DuplicateQualName qn)
     liftIO $ writeIORef (scQualNameEnv sc) (Map.insert qn i qns)
     liftIO $ modifyIORef' (scDisplayNameEnv sc) $ extendDisplayNameEnv i (nameAliases nmi)

-- | Generate a 'Name' with a fresh 'VarIndex' for the given
-- 'NameInfo' and register everything together in the naming
-- environment of the 'SharedContext'.
scmRegisterName :: NameInfo -> SCM Name
scmRegisterName nmi =
  do i <- scmFreshVarIndex
     scmRegisterNameWithIndex i nmi
     pure (Name i nmi)

scResolveQualName :: SharedContext -> QN.QualName -> IO (Maybe VarIndex)
scResolveQualName sc qn =
  do env <- readIORef (scQualNameEnv sc)
     pure $! Map.lookup qn env

-- | Create a unique global name with the given base name.
scmFreshName :: Text -> SCM Name
scmFreshName x =
  do i <- scmFreshVarIndex
     let qn = scFreshQualName x i
     let nmi = ImportedName qn (QN.aliases qn)
     scmRegisterNameWithIndex i nmi
     pure (Name i nmi)

-- | Create a 'VarName' with the given identifier (which may be "_").
scmFreshVarName :: Text -> SCM VarName
scmFreshVarName x = VarName <$> scmFreshVarIndex <*> pure x

-- | Returns shared term associated with ident.
-- Does not check module namespace.
scmGlobalDef :: Ident -> SCM Term
scmGlobalDef ident =
  do sc <- scmSharedContext
     m <- liftIO $ readIORef (scGlobalEnv sc)
     case HMap.lookup ident m of
       Nothing -> scmError (IdentNotFound ident)
       Just t -> pure t

-- | Internal function to register an 'Ident' with a 'Term' (which
-- must be a 'Constant' term with the same 'Ident') in the
-- 'scGlobalEnv' map of the 'SharedContext'. Not exported.
scmRegisterGlobal :: Ident -> Term -> SCM ()
scmRegisterGlobal ident t =
  do sc <- scmSharedContext
     dup <- liftIO $ atomicModifyIORef' (scGlobalEnv sc) f
     when dup $ scmError (DuplicateQualName (moduleIdentToQualName ident))
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

-- | Get the current 'ModuleMap'
scmGetModuleMap :: SCM ModuleMap
scmGetModuleMap =
  do sc <- scmSharedContext
     liftIO $ readIORef (scModuleMap sc)

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
-- the 'SharedContext'.
-- Throws an exception if the name is already registered.
scmInsDefInMap :: Def -> SCM ()
scmInsDefInMap d =
  do sc <- scmSharedContext
     e <-
       liftIO $ atomicModifyIORef' (scModuleMap sc) $ \mm ->
       case insDefInMap d mm of
         Left nm -> (mm, Just (AlreadyDefined nm))
         Right mm' -> (mm', Nothing)
     maybe (pure ()) scmError e

-- | Internal function to extend the SAWCore global environment with a
-- new constant, which may or may not have a definition. Not exported.
-- Assumes that the type and body (if present) are closed and valid
-- (according to 'scmEnsureValidTerm'), and that the body has the
-- given type.
scmDeclareDef :: Name -> DefQualifier -> Term -> Maybe Term -> SCM Term
scmDeclareDef nm q ty body =
  do scmInsDefInMap $
       Def
       { defName = nm
       , defQualifier = q
       , defType = ty
       , defBody = body
       }
     t <- scmConst nm
     -- Register constant in scGlobalEnv if it has an Ident name
     case nameInfo nm of
       ModuleIdentifier ident -> scmRegisterGlobal ident t
       ImportedName{} -> pure ()
     pure t

-- | Declare a SAW core primitive of the specified type.
scmDeclarePrim :: Ident -> DefQualifier -> Term -> SCM ()
scmDeclarePrim ident q def_tp =
  do scmEnsureValidTerm def_tp
     _ <- scmEnsureSortType def_tp
     let nmi = ModuleIdentifier ident
     nm <- scmRegisterName nmi
     _ <- scmDeclareDef nm q def_tp Nothing
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
-- Data Types

data DataTypeSpec =
  DataTypeSpec
  { dtsNameInfo :: NameInfo
    -- ^ The name of this data type
  , dtsParams :: [(VarName, Term)]
    -- ^ The context of parameters of this data type.
    -- Earlier variable names in the list are in scope.
  , dtsIndices :: [(VarName, Term)]
    -- ^ The context of indices of this data type.
    -- Earlier variable names and 'dtsParams' are in scope.
  , dtsSort :: Sort
    -- ^ The universe of this data type.
  , dtsCtors :: [CtorSpec]
    -- ^ The list of constructors of this data type.
    -- Variables from 'dtsParams' are in scope.
  , dtsMotiveName :: VarName
    -- ^ Variable name to use for the motive parameter of the recursor.
  , dtsArgName :: VarName
    -- ^ Variable name to use for the data argument of the recursor.
  }

data CtorSpec =
  CtorSpec
  { cspecNameInfo :: NameInfo
    -- ^ The name of this constructor
  , cspecArgs :: [(VarName, CtorArg)]
    -- ^ The argument types of this constructor.
    -- Earlier variables and 'dtsParams' (from the enclosing
    -- 'DataTypeSpec') are in scope.
  , cspecIndices :: [Term]
    -- ^ The indices of the result type of this constructor.
    -- Variables from 'dtsParams' (in the enclosing 'DataTypeSpec')
    -- and 'cspecArgs' are in scope.
  }

-- | Define a new data type with constructors in the global context.
-- Return the type constructor and data constructors as 'Term's.
-- Throw an error if the data type declaration is not well-formed:
-- Parameters, indices and constructor arguments must refer only to
-- bound variables and inhabit the appropriate sorts.
scmDefineDataType :: DataTypeSpec -> SCM (Term, [Term])
scmDefineDataType dts =
  do dName <- scmRegisterName (dtsNameInfo dts)
     -- Enforce that sorts of dtsParams do not exceed dtsSort
     let checkParam (x, ty) =
           do paramSort <- scmEnsureSortType ty
              unless (paramSort <= sortOf (dtsSort dts)) $
                scmError (DataTypeParameterSort dName (dtsSort dts) x ty)
     unless (dtsSort dts == PropSort) $ mapM_ checkParam (dtsParams dts)
     -- Enforce that sorts of dtsIndices are strictly contained in dtsSort
     let checkIndex (x, ty) =
           do indexSort <- scmEnsureSortType ty
              unless (indexSort <= dtsSort dts) $
                scmError (DataTypeIndexSort dName (dtsSort dts) x ty)
     unless (dtsSort dts == PropSort) $ mapM_ checkIndex (dtsIndices dts)
     -- Construct the kind of the data type
     s <- scmSort (dtsSort dts)
     dType <- scmPiList (dtsParams dts ++ dtsIndices dts) s
     -- Enforce that dType has no free variables.
     unless (closedTerm dType) $
       scmError (DataTypeKindNotClosed dName dType)
     -- NOTE: We can't use 'scmConst' with 'dName' because we haven't yet
     -- registered the name with its definition in the global context.
     -- We need to use the internal function 'scmMakeTerm' instead.
     let dSortOrType = maybe (Right dType) Left (asSort dType)
     d <- scmMakeTerm IntMap.empty (Constant dName) dSortOrType
            -- | DataTypeKindNotClosed Name Term
     params <- scmVariables (dtsParams dts)
     d_params <- scmApplyAll d params
     let ctorArgType :: CtorArg -> SCM Term
         ctorArgType (ConstArg tp) = pure tp
         ctorArgType (RecursiveArg zs ixs) =
           scmPiList zs =<< scmApplyAll d_params ixs
     let ctorSpecType :: Name -> CtorSpec -> SCM Term
         ctorSpecType cName cspec =
           do d_params_ixs <- scmApplyAll d_params (cspecIndices cspec)
              bs <- traverse (traverse ctorArgType) (cspecArgs cspec)
              body <- scmPiList bs d_params_ixs
              -- Enforce that the type of body is contained in dtsSort
              cSort <- scmEnsureSortType body
              unless (cSort <= dtsSort dts) $
                scmError (DataTypeCtorSort dName (dtsSort dts) cName body)
              -- Build constructor type
              scmPiList (dtsParams dts) body
     let makeCtor :: CtorSpec -> SCM Ctor
         makeCtor cs =
           do cName <- scmRegisterName (cspecNameInfo cs)
              cType <- ctorSpecType cName cs
              -- Enforce that cType is closed.
              unless (closedTerm cType) $
                scmError (DataTypeCtorNotClosed dName cName cType)
              pure $
                Ctor
                { ctorName = cName
                , ctorArgStruct =
                  CtorArgStruct
                  { ctorParams = dtsParams dts
                  , ctorArgs = cspecArgs cs
                  , ctorIndices = cspecIndices cs
                  }
                , ctorDataType = dName
                , ctorType = cType
                }
     ctors <- traverse makeCtor (dtsCtors dts)
     let dt =
           DataType
           { dtName = dName
           , dtParams = dtsParams dts
           , dtIndices = dtsIndices dts
           , dtSort = dtsSort dts
           , dtCtors = ctors
           , dtType = dType
           , dtMotiveName = dtsMotiveName dts
           , dtArgName = dtsArgName dts
           }
     -- Register the data type in the ModuleMap.
     sc <- scmSharedContext
     liftIO $ modifyIORef' (scModuleMap sc) $ \mm ->
       case insTypeDeclInMap dt mm of
         -- This should never happen; duplicate names are detected by scRegisterName.
         Left nm -> panic "scmDefineDataType" ["Duplicate name: " <> toAbsoluteName (nameInfo nm)]
         Right mm' -> mm'
     -- Register data type constant in scGlobalEnv if it has an Ident name.
     case dtsNameInfo dts of
       ImportedName{} -> pure ()
       ModuleIdentifier i -> scmRegisterGlobal i d
     -- Register constructors in scGlobalEnv if they have Ident names.
     cs <-
       forM ctors $ \ctor ->
       do c <- scmConst (ctorName ctor)
          case nameInfo (ctorName ctor) of
            ImportedName{} -> pure ()
            ModuleIdentifier i -> scmRegisterGlobal i c
          pure c
     -- Return Terms for data type and constructors.
     pure (d, cs)

--------------------------------------------------------------------------------
-- Recursors

scmRecursor :: Name -> Sort -> SCM Term
scmRecursor nm s =
  do sc <- scmSharedContext
     mm <- liftIO $ scGetModuleMap sc
     case lookupVarIndexInMap (nameIndex nm) mm of
       Just (ResolvedDataType dt) ->
         do unless (allowedElimSort dt s) $ scmError (RecursorPropElim nm s)
            let d = dtName dt
            let nparams = length (dtParams dt)
            let nixs = length (dtIndices dt)
            let ctorOrder = map ctorName (dtCtors dt)
            let crec = CompiledRecursor d s nparams nixs ctorOrder
            let vt = IntMap.empty
            let tf = FTermF (Recursor crec)
            ty <- scmRecursorType dt s
            scmMakeTerm vt tf (Right ty)
       _ ->
         scmError (DataTypeNotFound nm)

-- | Test whether a 'DataType' can be eliminated to the given sort. The rules
-- are that you can only eliminate propositional datatypes to the proposition
-- sort, unless your propositional data type is the empty type. This differs
-- slightly from the Rocq rules, which allow elimination of propositional
-- datatypes with a single constructor that has only propositional arguments,
-- but this Rocq behavior can be simulated with the behavior we are using here.
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
  Name {- ^ data type name -} ->
  Name {- ^ constructor name -} ->
  Term {- ^ motive function -} ->
  CtorArgStruct ->
  SCM Term
ctxCtorElimType d c p_ret (CtorArgStruct{..}) =
  do params <- scmVariables ctorParams
     d_params <- scmConstApply d params
     let helper :: [Term] -> [(VarName, CtorArg)] -> SCM Term
         helper prevs ((nm, ConstArg tp) : args) =
           -- For a constant argument type, just abstract it and continue
           do arg <- scmVariable nm tp
              rest <- helper (prevs ++ [arg]) args
              scmPi nm tp rest
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
           do d_params_ts <- scmApplyAll d_params ts
              -- Build the type of the argument arg
              arg_tp <- scmPiList zs d_params_ts
              arg <- scmVariable nm arg_tp
              -- Build the type of ih
              pret_ts <- scmApplyAll p_ret ts
              z_vars <- scmVariables zs
              arg_zs <- scmApplyAll arg z_vars
              ih_ret <- scmApply pret_ts arg_zs
              ih_tp <- scmPiList zs ih_ret
              -- Finally, build the pi-abstraction for arg and ih around the rest
              rest <- helper (prevs ++ [arg]) args
              scmPi nm arg_tp =<< scmFun ih_tp rest
         helper prevs [] =
           -- If we are finished with our arguments, construct the final result type
           -- (p_ret ret_ixs (c params prevs))
           do p_ret_ixs <- scmApplyAll p_ret ctorIndices
              appliedCtor <- scmConstApply c (params ++ prevs)
              scmApply p_ret_ixs appliedCtor
     helper [] ctorArgs

-- | Reduce an application of a recursor to a particular constructor.
-- This is known in the Rocq literature as an iota reduction. More specifically,
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
  Term {- ^ recursor applied to params, motive, and eliminator functions -} ->
  Term {- ^ constructor eliminator function -} ->
  [Term] {- ^ constructor arguments -} ->
  CtorArgStruct {- ^ constructor formal argument descriptor -} ->
  SCM Term
ctxReduceRecursor r elimf c_args CtorArgStruct{..}
  | length c_args /= length ctorArgs = panic "ctxReduceRecursor" ["Wrong number of constructor arguments"]
  | otherwise =
    do args <- mk_args IntMap.empty (zip c_args ctorArgs)
       scmApplyAllBeta elimf args
  where
    mk_args :: IntMap Term ->  -- already processed parameters/arguments
               [(Term, (VarName, CtorArg))] ->
                 -- remaining actual arguments to process, with
                 -- telescope for typing the actual arguments
               SCM [Term]
    -- no more arguments to process
    mk_args _ [] = return []

    -- process an argument that is not a recursive call
    mk_args pre_xs ((x, (nm, ConstArg _)) : xs_args) =
      do tl <- mk_args (IntMap.insert (vnIndex nm) x pre_xs) xs_args
         pure (x : tl)

    -- process an argument that is a recursive call
    mk_args pre_xs ((x, (nm, RecursiveArg zs ixs)) : xs_args) =
      do zs'  <- traverse (traverse (scmInstantiate pre_xs)) zs
         ixs' <- traverse (scmInstantiate pre_xs) ixs
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
      SCM Term
    mk_rec_arg zs_ctx ixs x =
      -- eta expand over the zs and apply the Recursor form
      do zs <- scmVariables zs_ctx
         x_zs <- scmApplyAll x zs
         r_ixs <- scmApplyAll r ixs
         body <- scmApply r_ixs x_zs
         scmLambdaList zs_ctx body

-- | Build the type of the @p_ret@ function, also known as the "motive"
-- function, of a recursor on datatype @d@. This type has the form
--
-- > (i1::ix1) -> .. -> (im::ixm) -> d p1 .. pn i1 .. im -> s
--
-- where the @pi@ are the parameters of @d@, the @ixj@ are the indices
-- of @d@, and @s@ is any sort supplied as an argument.
-- Parameter variables @p1 .. pn@ will be free in the resulting term.
scmRecursorMotiveType :: DataType -> Sort -> SCM Term
scmRecursorMotiveType dt s =
  do param_vars <- scmVariables (dtParams dt)
     ix_vars <- scmVariables (dtIndices dt)
     d <- scmConstApply (dtName dt) (param_vars ++ ix_vars)
     ret <- scmFun d =<< scmSort s
     scmPiList (dtIndices dt) ret

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
scmRecursorAppType :: DataType -> Term -> SCM Term
scmRecursorAppType dt motive =
  do param_vars <- scmVariables (dtParams dt)
     ix_vars <- scmVariables (dtIndices dt)
     d <- scmConstApply (dtName dt) (param_vars ++ ix_vars)
     let arg_vn = dtArgName dt
     arg_var <- scmVariable arg_vn d
     ret <- scmApplyAll motive (ix_vars ++ [arg_var])
     scmPiList (dtIndices dt ++ [(arg_vn, d)]) ret

-- | Build the full type of an unapplied recursor for datatype @d@
-- with elimination to sort @s@.
-- This type has the form
--
-- > (p1:pt1) -> .. -> (pn::ptn) ->
-- > (motive : (i1::ix1) -> .. -> (im::ixm) -> d p1 .. pn i1 .. im -> s) ->
-- > (elim1 : ..) -> .. (elimk : ..) ->
-- > (i1:ix1) -> .. -> (im:ixm) ->
-- >   (arg : d p1 .. pn i1 .. im) -> motive i1 .. im arg
scmRecursorType :: DataType -> Sort -> SCM Term
scmRecursorType dt s =
  do let d = dtName dt

     -- Compute the type of the motive function, which has the form
     -- (i1:ix1) -> .. -> (im:ixm) -> d p1 .. pn i1 .. im -> s
     motive_ty <- scmRecursorMotiveType dt s
     let motive_vn = dtMotiveName dt
     motive_var <- scmVariable motive_vn motive_ty

     -- Compute the types of the elimination functions
     elims_tps <-
       forM (dtCtors dt) $ \ctor ->
       ctxCtorElimType d (ctorName ctor) motive_var (ctorArgStruct ctor)

     scmPiList (dtParams dt) =<<
       scmPi motive_vn motive_ty =<<
       scmFunAll elims_tps =<<
       scmRecursorAppType dt motive_var

-- | Reduce an application of a recursor. This is known in the Rocq literature as
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
-- @xi@. See the documentation for 'ctxReduceRecursor' for more details.
scmReduceRecursor ::
  Term {- ^ recursor term -} ->
  CompiledRecursor {- ^ concrete data included in the recursor term -} ->
  [Term] {- ^ datatype parameters -} ->
  Term {- ^ motive function -} ->
  [Term] {- ^ eliminator functions -} ->
  Name {- ^ constructor name -} ->
  [Term] {- ^ constructor arguments -} ->
  SCM Term
scmReduceRecursor r crec params motive elims c args =
  do mres <- lookupVarIndexInMap (nameIndex c) <$> scmGetModuleMap
     let cs_fs = Map.fromList (zip (map nameIndex (recursorCtorOrder crec)) elims)
     r_applied <- scmApplyAll r (params ++ motive : elims)
     case mres of
       Just (ResolvedCtor ctor) ->
         ctorIotaReduction ctor r_applied cs_fs args
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
  Ctor ->
  Term {- ^ recursor term -} ->
  Map VarIndex Term {- ^ constructor eliminators -} ->
  [Term] {- ^ constructor arguments -} ->
  SCM Term
ctorIotaReduction ctor r cs_fs args =
  ctxReduceRecursor r elim args (ctorArgStruct ctor)
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
scmWhnf :: Term -> SCM Term
scmWhnf t0 = go [] t0
  where
    go :: [WHNFElim] -> Term -> SCM Term
    go xs                     (asApp            -> Just (t, x)) = go (ElimApp x : xs) t
    go xs                     (asRecordSelector -> Just (t, n)) = go (ElimProj n : xs) t
    go xs                     (asPairSelector -> Just (t, i))   = go (ElimPair i : xs) t
    go (ElimApp x : xs)       (asLambda -> Just (vn, _, body))  = betaReduce xs [(vn, x)] body
    go (ElimPair i : xs)      (asPairValue -> Just (a, b))      = go xs (if i then b else a)
    go (ElimProj fld : xs)    (asRecordValue -> Just elems)     = case lookup fld elems of
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
                                                                                scmReduceRecursor rt crec params motive elims nm args' >>= go xs'
                                                                       ResolvedDataType _ ->
                                                                         foldM reapply t xs

    go xs                     t                                 = foldM reapply t xs

    betaReduce :: [WHNFElim] -> [(VarName, Term)] -> Term -> SCM Term
    betaReduce (ElimApp x : xs) vs (asLambda -> Just (vn,_,body)) =
      betaReduce xs ((vn, x) : vs) body
    betaReduce xs vs body =
      do let subst = IntMap.fromList [ (vnIndex vn, x) | (vn, x) <- vs ]
         body' <- scmInstantiate subst body
         go xs body'

    reapply :: Term -> WHNFElim -> SCM Term
    reapply t (ElimApp x) = scmApply t x
    reapply t (ElimProj i) = scmRecordSelect t i
    reapply t (ElimPair i) = scmPairSelector t i
    reapply t (ElimRecursor r _crec params motive elims ixs) =
      do f <- scmApplyAll r (params ++ motive : elims ++ ixs)
         scmApply f t

    resolveConstant :: Name -> SCM ResolvedName
    resolveConstant nm = requireNameInMap nm <$> scmGetModuleMap

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

-- | Test if two terms are convertible up to the reductions performed
-- by 'scmWhnf'.
scmConvertible ::
  Term ->
  Term ->
  SCM Bool
scmConvertible tm1 tm2 =
  do c <- newIntCache
     go c emptyVarCtx emptyVarCtx tm1 tm2

  where
    whnf :: IntCache SCM Term -> Term -> SCM (TermF Term)
    whnf c t@STApp{stAppIndex = idx} =
      unwrapTermF <$> useIntCache c idx (scmWhnf t)

    go :: IntCache SCM Term -> VarCtx -> VarCtx -> Term -> Term -> SCM Bool
    go c env1@(VarCtx _ m1) env2@(VarCtx _ m2) t1 t2
      | termIndex t1 == termIndex t2 &&
        -- bound variables must also refer to the same de Bruijn indices
        IntMap.intersection m1 (varTypes t1) ==
        IntMap.intersection m2 (varTypes t2) = pure True -- succeed early case
      | otherwise =
        do tf1 <- whnf c t1
           tf2 <- whnf c t2
           goF c env1 env2 tf1 tf2

    goF :: IntCache SCM Term -> VarCtx -> VarCtx -> TermF Term -> TermF Term -> SCM Bool

    goF _c _env1 _env2 (Constant nm1) (Constant nm2)
      | nameIndex nm1 == nameIndex nm2 = pure True

    goF c env1 env2 (FTermF ftf1) (FTermF ftf2) =
      case zipWithFlatTermF (go c env1 env2) ftf1 ftf2 of
        Nothing -> pure False
        Just zipped -> Fold.and <$> traverse id zipped

    goF c env1 env2 (App f1 u1) (App f2 u2) =
      do a <- go c env1 env2 f1 f2
         b <- go c env1 env2 u1 u2
         pure (a && b)

    goF c env1 env2 (Lambda x1 ty1 body1) (Lambda x2 ty2 body2) =
      do a <- go c env1 env2 ty1 ty2
         b <- go c (consVarCtx x1 env1) (consVarCtx x2 env2) body1 body2
         pure (a && b)

    goF c env1 env2 (Pi x1 ty1 body1) (Pi x2 ty2 body2) =
      do a <- go c env1 env2 ty1 ty2
         b <- go c (consVarCtx x1 env1) (consVarCtx x2 env2) body1 body2
         pure (a && b)

    goF c env1 env2 (Variable x1 t1) (Variable x2 t2) =
      case (lookupVarCtx x1 env1, lookupVarCtx x2 env2) of
        (Just i1, Just i2) | i1 == i2 -> pure True
        (Nothing, Nothing) | x1 == x2 -> go c env1 env2 t1 t2
        _ -> pure False

    -- final catch-all case
    goF _c _env1 _env2 _t1 _t2 = pure False

-- | Check whether one type is a subtype of another: Either they are
-- convertible, or they are both Pi types with convertible argument
-- types and result sorts @s1@ and @s2@ with @s1 <= s2@.
scmSubtype :: Term -> Term -> SCM Bool
scmSubtype t1 t2
  | alphaEquiv t1 t2 = pure True
  | otherwise =
    do t1' <- scmWhnf t1
       t2' <- scmWhnf t2
       case (t1', t2') of
         (asSort -> Just s1, asSort -> Just s2) ->
           pure (s1 <= s2)
         (unwrapTermF -> Pi x1 a1 b1, unwrapTermF -> Pi x2 a2 b2)
           | x1 == x2 ->
             (&&) <$> scmConvertible a1 a2 <*> scmSubtype b1 b2
           | otherwise ->
             do conv1 <- scmConvertible a1 a2
                var1 <- scmVariable x1 a1
                b2' <- scmInstantiate (IntMap.singleton (vnIndex x2) var1) b2
                conv2 <- scmSubtype b1 b2'
                pure (conv1 && conv2)
         _ ->
           scmConvertible t1' t2'


--------------------------------------------------------------------------------
-- Type checking

-- | Look up the type of a global constant, given its 'Name'.
scmTypeOfName :: Name -> SCM Term
scmTypeOfName nm =
  do sc <- scmSharedContext
     mm <- liftIO $ scGetModuleMap sc
     case lookupVarIndexInMap (nameIndex nm) mm of
       Just r -> pure (resolvedNameType r)
       Nothing -> scmError (NameNotFound nm)

-- | Return the type of a term.
scmTypeOf :: Term -> SCM Term
scmTypeOf t =
  case stAppType t of
    Right ty -> pure ty
    Left s -> scmSort s

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
scmInstantiateBeta :: IntMap Term -> Term -> SCM Term
scmInstantiateBeta sub t0 =
  do let domainVars = IntMap.keysSet sub
     let rangeVars = foldMap freeVars sub
     cache <- newIntCache
     let memo :: Term -> SCM Term
         memo t@STApp{stAppIndex = i} = useIntCache cache i (go t)
         go :: Term -> SCM Term
         go t
           | IntSet.disjoint domainVars (freeVars t) = pure t
           | otherwise = goArgs t []
         goArgs :: Term -> [Term] -> SCM Term
         goArgs t args =
           case unwrapTermF t of
             FTermF ftf ->
               do ftf' <- traverse memo ftf
                  t' <- scmFlatTermF ftf'
                  scmApplyAll t' args
             App t1 t2 ->
               do t2' <- memo t2
                  goArgs t1 (t2' : args)
             Lambda x t1 t2 ->
               do t1' <- memo t1
                  (x', t2') <- goBinder x t1' t2
                  t' <- scmLambda x' t1' t2'
                  scmApplyAll t' args
             Pi x t1 t2 ->
               do t1' <- memo t1
                  (x', t2') <- goBinder x t1' t2
                  t' <- scmPi x' t1' t2'
                  scmApplyAll t' args
             Constant {} ->
               scmApplyAll t args
             Variable x t1 ->
               case IntMap.lookup (vnIndex x) sub of
                 Just t' -> scmApplyAllBeta t' args
                 Nothing ->
                   do t1' <- memo t1
                      t' <- scmVariable x t1'
                      scmApplyAll t' args
         goBinder :: VarName -> Term -> Term -> SCM (VarName, Term)
         goBinder x@(vnIndex -> i) t body
           | IntSet.member i rangeVars =
               -- Possibility of capture; rename bound variable.
               do x' <- scmFreshVarName (vnName x)
                  var <- scmVariable x' t
                  let sub' = IntMap.insert i var sub
                  body' <- scmInstantiateBeta sub' body
                  pure (x', body')
           | IntMap.member i sub =
               -- Shadowing; remove entry from substitution.
               do let sub' = IntMap.delete i sub
                  body' <- scmInstantiateBeta sub' body
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
scmApplyAllBeta :: Term -> [Term] -> SCM Term
scmApplyAllBeta t0 [] = pure t0
scmApplyAllBeta t0 (arg0 : args0) =
  case asLambda t0 of
    Nothing -> scmApplyAll t0 (arg0 : args0)
    Just (x, _, body) -> go (IntMap.singleton (vnIndex x) arg0) body args0
  where
    go :: IntMap Term -> Term -> [Term] -> SCM Term
    go sub (asLambda -> Just (x, _, body)) (arg : args) =
      go (IntMap.insert (vnIndex x) arg sub) body args
    go sub t args =
      do t' <- scmInstantiateBeta sub t
         scmApplyAllBeta t' args


--------------------------------------------------------------------------------
-- Building shared terms

-- | Apply a function 'Term' to zero or more argument 'Term's.
scmApplyAll :: Term -> [Term] -> SCM Term
scmApplyAll = foldlM scmApply

-- | Create a term from a 'Sort'.
scmSort :: Sort -> SCM Term
scmSort s = scmSortWithFlags s noFlags

-- | Create a term from a 'Sort', and set the given advisory flags
scmSortWithFlags :: Sort -> SortFlags -> SCM Term
scmSortWithFlags s flags =
  scmMakeTerm IntMap.empty (FTermF (Sort s flags)) (Left (sortOf s))

-- | Create a literal term from a 'Natural'.
scmNat :: Natural -> SCM Term
scmNat 0 = scmGlobalDef "Prelude.Zero"
scmNat n =
  do p <- scmPos n
     scmGlobalApply "Prelude.NatPos" [p]

scmPos :: Natural -> SCM Term
scmPos n
  | n <= 1 = scmGlobalDef "Prelude.One"
  | otherwise =
    do arg <- scmPos (div n 2)
       let ident = if even n then "Prelude.Bit0" else "Prelude.Bit1"
       scmGlobalApply ident [arg]

-- | Create a literal term (of saw-core type @String@) from a 'Text'.
scmString :: Text -> SCM Term
scmString s =
  do ty <- scmStringType
     scmMakeTerm IntMap.empty (FTermF (StringLit s)) (Right ty)

-- | Create a term representing the primitive saw-core type @String@.
scmStringType :: SCM Term
scmStringType = scmGlobalDef preludeStringIdent

-- | Create a vector term from a type (as a 'Term') and a list of 'Term's of
-- that type.
scmVector :: Term -> [Term] -> SCM Term
scmVector e xs =
  do scmEnsureValidTerm e
     vt <- foldM (scmUnifyVarTypes "scVector") (varTypes e) (map varTypes xs)
     let check x =
           do scmEnsureValidTerm x
              xty <- scmTypeOf x
              ok <- scmSubtype xty e
              unless ok $ scmError (VectorNotSubtype e x)
     mapM_ check xs
     n <- scmNat (fromIntegral (length xs))
     let tf = FTermF (ArrayValue e (V.fromList xs))
     ty <- scmVecType n e
     scmMakeTerm vt tf (Right ty)

-- | Create a term representing a vector type, from a term giving the length
-- and a term giving the element type.
scmVecType :: Term -> Term -> SCM Term
scmVecType n e = scmGlobalApply preludeVecIdent [n, e]

-- | Create a record term from a list of record fields.
scmRecordValue :: [(FieldName, Term)] -> SCM Term
scmRecordValue [] =
  scmGlobalDef "Prelude.Empty"
scmRecordValue ((fname, x) : fields) =
  do s <- scmString fname
     a <- scmTypeOf x
     y <- scmRecordValue fields
     b <- scmTypeOf y
     scmGlobalApply "Prelude.RecordValue" [s, a, b, x, y]

-- | Create a record field access term from a 'Term' representing a record and
-- a 'FieldName'.
scmRecordSelect :: Term -> FieldName -> SCM Term
scmRecordSelect t0 fname =
  do ty0 <- scmTypeOf t0
     go t0 ty0
  where
    go :: Term -> Term -> SCM Term
    go t ty =
      do result <- scmEnsureRecognizer (NotRecord t0) asRecordTy ty
         case result of
           Nothing -> scmError (FieldNotFound t0 fname)
           Just (f, s, a, b)
             | f == fname ->
               scmGlobalApply "Prelude.headRecord" [s, a, b, t]
             | otherwise ->
               do y <- scmGlobalApply "Prelude.tailRecord" [s, a, b, t]
                  go y b
    asRecordTy :: Term -> Maybe (Maybe (Text, Term, Term, Term))
    asRecordTy t =
      case isGlobalDef "Prelude.EmptyType" t of
        Just () -> Just Nothing
        Nothing ->
          do (t1, b) <- asApp t
             (t2, a) <- asApp t1
             (t3, s) <- asApp t2
             f <- asStringLit s
             () <- isGlobalDef "Prelude.RecordType" t3
             Just (Just (f, s, a, b))

-- | Create a term representing the type of a record from a list associating
-- field names (as 'FieldName's) and types (as 'Term's). Note that the order of
-- the given list is irrelevant, as record fields are not ordered.
scmRecordType :: [(FieldName, Term)] -> SCM Term
scmRecordType [] = scmGlobalDef "Prelude.EmptyType"
scmRecordType ((fname, a) : fields) =
  do s <- scmString fname
     b <- scmRecordType fields
     scmGlobalApply "Prelude.RecordType" [s, a, b]

-- | Create a unit-valued term.
scmUnitValue :: SCM Term
scmUnitValue =
  do ty <- scmUnitType
     scmMakeTerm IntMap.empty (FTermF UnitValue) (Right ty)

-- | Create a term representing the unit type.
scmUnitType :: SCM Term
scmUnitType =
  scmMakeTerm IntMap.empty (FTermF UnitType) (Left (TypeSort 0))

-- | Create a pair term from two terms.
scmPairValue ::
  Term {- ^ The left projection -} ->
  Term {- ^ The right projection -} ->
  SCM Term
scmPairValue t1 t2 =
  do scmEnsureValidTerm t1
     scmEnsureValidTerm t2
     vt <- scmUnifyVarTypes "scPairValue" (varTypes t1) (varTypes t2)
     let tf = FTermF (PairValue t1 t2)
     ty1 <- scmTypeOf t1
     ty2 <- scmTypeOf t2
     ty <- scmPairType ty1 ty2
     scmMakeTerm vt tf (Right ty)

-- | Create a term representing a pair type from two other terms, each
-- representing a type.
scmPairType ::
  Term {- ^ Left projection type -} ->
  Term {- ^ Right projection type -} ->
  SCM Term
scmPairType t1 t2 =
  do scmEnsureValidTerm t1
     scmEnsureValidTerm t2
     vt <- scmUnifyVarTypes "scPairType" (varTypes t1) (varTypes t2)
     let tf = FTermF (PairType t1 t2)
     s1 <- scmEnsureSortType t1
     s2 <- scmEnsureSortType t2
     scmMakeTerm vt tf (Left (max s1 s2))

-- | Create a term giving the left projection of a 'Term' representing a pair.
scmPairLeft :: Term -> SCM Term
scmPairLeft t =
  do scmEnsureValidTerm t
     (ty, _) <- scmEnsurePairType t
     let mty = maybe (Right ty) Left (asSort ty)
     scmMakeTerm (varTypes t) (FTermF (PairLeft t)) mty

-- | Create a term giving the right projection of a 'Term' representing a pair.
scmPairRight :: Term -> SCM Term
scmPairRight t =
  do scmEnsureValidTerm t
     (_, ty) <- scmEnsurePairType t
     let mty = maybe (Right ty) Left (asSort ty)
     scmMakeTerm (varTypes t) (FTermF (PairRight t)) mty

-- | Create a term representing either the left or right projection of the
-- given 'Term', depending on the given 'Bool': left if @False@, right if @True@.
scmPairSelector :: Term -> Bool -> SCM Term
scmPairSelector t False = scmPairLeft t
scmPairSelector t True = scmPairRight t

-- | Create a term representing the type of a non-dependent function, given a
-- parameter and result type (as 'Term's).
scmFun ::
  Term {- ^ The parameter type -} ->
  Term {- ^ The result type -} ->
  SCM Term
scmFun a b = scmPi wildcardVarName a b

-- | Create a term representing the type of a non-dependent n-ary function,
-- given a list of parameter types and a result type (as terms).
scmFunAll ::
  [Term] {- ^ The parameter types -} ->
  Term {- ^ The result type -} ->
  SCM Term
scmFunAll argTypes resultType = foldrM scmFun resultType argTypes

-- | Create a lambda term of multiple arguments (curried) from a list
-- associating parameter names to types (as 'Term's) and a body.
-- The parameters are listed outermost first.
-- Variable names in the parameter list are in scope for all parameter
-- types occurring later in the list.
scmLambdaList ::
  [(VarName, Term)] {- ^ List of parameter / parameter type pairs -} ->
  Term {- ^ The body -} ->
  SCM Term
scmLambdaList [] body = pure body
scmLambdaList ((x, t) : xts) body =
  scmLambda x t =<< scmLambdaList xts body

-- | Create a (possibly dependent) function of multiple arguments (curried)
-- from a list associating parameter names to types (as 'Term's) and a body.
-- Variable names in the parameter list are in scope for all parameter
-- types occurring later in the list.
scmPiList ::
  [(VarName, Term)] {- ^ List of parameter / parameter type pairs -} ->
  Term {- ^ The body -} ->
  SCM Term
scmPiList [] body = pure body
scmPiList ((x, t) : xts) body =
  scmPi x t =<< scmPiList xts body

-- | Define a global constant with the specified base name (as
-- 'Text') and body.
-- The term for the body must not have any free variables.
-- A globally-unique name with the specified base name will be created
-- using 'scFreshName'.
-- The type of the body determines the type of the constant; to
-- specify a different formulation of the type, use 'scAscribe'.
scmFreshConstant ::
  Text {- ^ The base name -} ->
  Term {- ^ The body -} ->
  SCM Term
scmFreshConstant name rhs =
  do scmEnsureValidTerm rhs
     nm <- scmFreshName name
     unless (closedTerm rhs) $ scmError (ConstantNotClosed nm rhs)
     ty <- scmTypeOf rhs
     scmDeclareDef nm NoQualifier ty (Just rhs)

-- | Define a global constant with the specified name (as 'NameInfo')
-- and body.
-- The QualName in the given 'NameInfo' must be globally unique.
-- The term for the body must not have any free variables.
-- The type of the body determines the type of the constant; to
-- specify a different formulation of the type, use 'scAscribe'.
scmDefineConstant ::
  NameInfo {- ^ The name -} ->
  Term {- ^ The body -} ->
  SCM Term
scmDefineConstant nmi rhs =
  do scmEnsureValidTerm rhs
     ty <- scmTypeOf rhs
     nm <- scmRegisterName nmi
     unless (closedTerm rhs) $
       scmError (ConstantNotClosed nm rhs)
     scmDeclareDef nm NoQualifier ty (Just rhs)

-- | Declare a global opaque constant with the specified name (as
-- 'NameInfo') and type.
-- Such a constant has no definition, but unlike a variable it may be
-- used in other constant definitions and is not subject to
-- lambda-binding or substitution.
scmOpaqueConstant ::
  NameInfo ->
  Term {- ^ type of the constant -} ->
  SCM Term
scmOpaqueConstant nmi ty =
  do scmEnsureValidTerm ty
     _ <- scmEnsureSortType ty
     nm <- scmRegisterName nmi
     scmDeclareDef nm NoQualifier ty Nothing

-- | Create a function application term from a global identifier and a list of
-- arguments (as 'Term's).
scmGlobalApply :: Ident -> [Term] -> SCM Term
scmGlobalApply i ts =
  do c <- scmGlobalDef i
     scmApplyAll c ts


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
       , scQualNameEnv = ur
       , scGlobalEnv = gr
       , scNextTermIndex = tr
       , scValidTerms = ir
       }

-- | Instantiate some of the named variables in the term.
-- The 'IntMap' is keyed by 'VarIndex'.
-- Note: The replacement is _not_ applied recursively
-- to the terms in the substitution map.
scmInstantiate :: IntMap Term -> Term -> SCM Term
scmInstantiate vmap t0 =
  do let domainVars = IntMap.keysSet vmap
     let rangeVars = foldMap freeVars vmap
     tcache <- newIntCache
     let memo :: Term -> SCM Term
         memo t = useIntCache tcache (termIndex t) (go t)
         go :: Term -> SCM Term
         go t
           | IntSet.disjoint domainVars (freeVars t) = pure t
           | otherwise =
             case unwrapTermF t of
               FTermF ftf ->
                 scmFlatTermF =<< traverse memo ftf
               App t1 t2 ->
                 do t1' <- memo t1
                    t2' <- memo t2
                    scmApply t1' t2'
               Lambda x t1 t2 ->
                 do t1' <- memo t1
                    (x', t2') <- goBinder x t1' t2
                    scmLambda x' t1' t2'
               Pi x t1 t2 ->
                 do t1' <- memo t1
                    (x', t2') <- goBinder x t1' t2
                    scmPi x' t1' t2'
               Constant {} -> pure t
               Variable nm tp ->
                 case IntMap.lookup (vnIndex nm) vmap of
                   Just t' -> pure t'
                   Nothing -> scmVariable nm =<< memo tp
         goBinder :: VarName -> Term -> Term -> SCM (VarName, Term)
         goBinder x@(vnIndex -> i) t body
           | IntSet.member i rangeVars =
               -- Possibility of capture; rename bound variable.
               do x' <- scmFreshVarName (vnName x)
                  var <- scmVariable x' t
                  let vmap' = IntMap.insert i var vmap
                  body' <- scmInstantiate vmap' body
                  pure (x', body')
           | IntMap.member i vmap =
               -- Shadowing; remove entry from substitution.
               do let vmap' = IntMap.delete i vmap
                  body' <- scmInstantiate vmap' body
                  pure (x, body')
           | otherwise =
               -- No possibility of shadowing or capture.
               do body' <- memo body
                  pure (x, body')
     go t0
