{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE CPP #-}

{- |
Module      : Verifier.SAW.SharedTerm
Copyright   : Galois, Inc. 2012-2014
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.SharedTerm
  ( TermF(..)
  , Uninterp(..)
  , Ident, mkIdent
  , VarIndex
  , ExtCns(..)
    -- * Shared terms
  , SharedTerm(..)
  , TermIndex
  , looseVars
  , unshare
  , alphaEquiv
    -- * SharedContext interface for building shared terms
  , SharedContext
  , mkSharedContext
    -- ** Low-level generic term constructors
  , scTermF
  , scFlatTermF
    -- ** Implicit versions of functions.
  , scDefTerm
  , scFreshGlobalVar
  , scFreshGlobal
  , scGlobalDef
  , scModule
  , scApply
  , scApplyAll
  , SharedTermExt(..)
  , scApplyExt
  , scRecord
  , scRecordSelect
  , scRecordType
  , scDataTypeApp
  , scCtorApp
  , scApplyCtor
  , scFun
  , scString
  , Nat
  , scNat
  , scNatType
  , scAddNat
  , scSubNat
  , scMulNat
  , scEqualNat
  , scLtNat

  , scBool
  , scBoolType
  , scFunAll
  , scLambda
  , scLambdaList
  , scPi
  , scPiList
  , scLocalVar
  , scLookupDef
  , scSort
  , scTuple
  , scTupleType
  , scTupleSelector
  , scVector
  , scVecType
  , scTermCount
  , scPrettyTerm
  , scPrettyTermDoc
  , scGlobalApply
  , scSharedTerm
  , scImport
    -- ** Normalization
  , scWhnf
    -- ** Type checking
  , scTypeOf
  , scTypeOf'
  , asSort
  , reducePi
  , scTypeOfCtor
  , scTypeOfDataType
  , scTypeOfGlobal
    -- ** Prelude operations
  , scAppend
  , scGet
  , scAt
  , scNot
  , scAnd
  , scOr
  , scXor
  , scBoolEq
  , scIte
  , scSingle
  , scSlice
    -- *** Bitvector primitives
  , scBitvector
  , scBvNat
  , scBvToNat
  , scBvAt
  , scBvConst
  , scFinVal
  , scBvAdd, scBvSub, scBvMul, scBvNeg
  , scBvURem, scBvUDiv, scBvSRem, scBvSDiv
  , scBvOr, scBvAnd, scBvXor
  , scBvNot
  , scBvEq, scBvUGe, scBvUGt, scBvULe, scBvULt
  , scBvSGt, scBvSGe, scBvSLt, scBvSLe
  , scBvShl, scBvShr, scBvSShr
  , scBvUExt, scBvSExt
  , scBvTrunc
    -- ** Utilities
--  , scTrue
--  , scFalse
    -- ** Variable substitution
  , instantiateVar
  , instantiateVarList
  , extIdx
  , extName
  , getAllExts
  , scInstantiateExt
  , scAbstractExts
  , incVars
  , scUnfoldConstants
  , scUnfoldConstants'
  , scSharedSize
  , scTreeSize
  ) where

import Control.Applicative
-- ((<$>), pure, (<*>))
import Control.Concurrent.MVar
import Control.Exception
import Control.Lens
import Control.Monad.Ref
import Control.Monad.State.Strict as State
import Data.Bits
import qualified Data.Foldable
import Data.Foldable (foldl', foldlM, foldrM, maximum)
import Data.Hashable (Hashable(..))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IORef (IORef)
import Data.List (sortBy)
import Data.Ord (comparing)

import Data.Map (Map)
import qualified Data.Map as Map
#if __GLASGOW_HASKELL__ < 706
import qualified Data.Map as StrictMap
#else
import qualified Data.Map.Strict as StrictMap
#endif
import qualified Data.Set as Set
import qualified Data.Traversable as T
import Data.Typeable
import qualified Data.Vector as V
import Data.Word
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.Leijen hiding ((<$>))

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.Recognizer
import Verifier.SAW.TypedAST hiding (incVars, instantiateVarList)
import qualified Verifier.SAW.TermNet as Net

newtype Uninterp s = Uninterp { getUninterp :: (String, SharedTerm s) } deriving Show

type TermIndex = Int -- Word64

data SharedTerm s
  = STApp {-# UNPACK #-} !TermIndex !(TermF (SharedTerm s))
  | Unshared !(TermF (SharedTerm s))
  deriving (Typeable)

instance Hashable (SharedTerm s) where
  hashWithSalt salt (STApp i _)  = salt `combine` 0x00000000 `hashWithSalt` hash i
  hashWithSalt salt (Unshared t) = salt `combine` 0x55555555 `hashWithSalt` hash t

-- | Combine two given hash values.  'combine' has zero as a left
-- identity. (FNV hash, copied from Data.Hashable 1.2.1.0.)
combine :: Int -> Int -> Int
combine h1 h2 = (h1 * 0x01000193) `xor` h2

instance Termlike (SharedTerm s) where
  unwrapTermF (STApp _ tf) = tf
  unwrapTermF (Unshared tf) = tf

instance Eq (SharedTerm s) where
  STApp i t  == STApp j u  = i == j || t == u
  STApp _ t  == Unshared u = t == u
  Unshared t == STApp _  u = t == u
  Unshared t == Unshared u = t == u

instance Ord (SharedTerm s) where
  compare (STApp i _) (STApp j _) | i == j = EQ
  compare x y = compare (unwrapTermF x) (unwrapTermF y)

instance Net.Pattern (SharedTerm s) where
  toPat = termToPat

------------------------------------------------------------
-- TermFMaps

data TermFMap s a
  = TermFMap
  { appMapTFM :: !(IntMap (IntMap a))
  , hashMapTFM :: !(HashMap (TermF (SharedTerm s)) a)
  }

emptyTFM :: TermFMap s a
emptyTFM = TermFMap IntMap.empty HMap.empty

lookupTFM :: TermF (SharedTerm s) -> TermFMap s a -> Maybe a
lookupTFM tf tfm =
  case tf of
    App (STApp i _) (STApp j _) ->
      IntMap.lookup i (appMapTFM tfm) >>= IntMap.lookup j
    _ -> HMap.lookup tf (hashMapTFM tfm)

insertTFM :: TermF (SharedTerm s) -> a -> TermFMap s a -> TermFMap s a
insertTFM tf x tfm =
  case tf of
    App (STApp i _) (STApp j _) ->
      let f Nothing = Just (IntMap.singleton j x)
          f (Just m) = Just (IntMap.insert j x m)
      in tfm { appMapTFM = IntMap.alter f i (appMapTFM tfm) }
    _ -> tfm { hashMapTFM = HMap.insert tf x (hashMapTFM tfm) }

----------------------------------------------------------------------
-- SharedContext: a high-level interface for building SharedTerms.

data SharedContext s = SharedContext
  { -- | Returns the current module for the underlying global theory.
    scModule        :: Module
  , scTermF         :: TermF (SharedTerm s) -> IO (SharedTerm s)
  , scFreshGlobalVar :: IO VarIndex
  }

scFlatTermF :: SharedContext s -> FlatTermF (SharedTerm s) -> IO (SharedTerm s)
scFlatTermF sc ftf = scTermF sc (FTermF ftf)

-- | Create a global variable with the given identifier (which may be "_") and type.
scFreshGlobal :: SharedContext s -> String -> SharedTerm s -> IO (SharedTerm s)
scFreshGlobal sc sym tp = do
  i <- scFreshGlobalVar sc
  scFlatTermF sc (ExtCns (EC i sym tp))

-- | Returns shared term associated with ident.
-- Does not check module namespace.
scGlobalDef :: SharedContext s -> Ident -> IO (SharedTerm s)
scGlobalDef sc ident = scFlatTermF sc (GlobalDef ident)

scApply :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scApply sc f = scTermF sc . App f

data SharedTermExt s
   = SharedTermApp (TermF (SharedTermExt s))
   | SharedTermVar (SharedTerm s)

scApplyExt :: SharedContext s -> SharedTermExt s -> IO (SharedTerm s)
scApplyExt _ (SharedTermVar v) = return v
scApplyExt sc (SharedTermApp tf) =
  scTermF sc =<< traverse (scApplyExt sc) tf

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scDataTypeApp :: SharedContext s -> Ident -> [SharedTerm s] -> IO (SharedTerm s)
scDataTypeApp sc ident args = scFlatTermF sc (DataTypeApp ident args)

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scCtorApp :: SharedContext s -> Ident -> [SharedTerm s] -> IO (SharedTerm s)
scCtorApp sc ident args = scFlatTermF sc (CtorApp ident args)

-- SharedContext implementation.

data AppCache s = AC { acBindings :: !(TermFMap s (SharedTerm s))
                     , acNextIdx :: !TermIndex
                     }

type AppCacheRef s = MVar (AppCache s)

emptyAppCache :: AppCache s
emptyAppCache = AC emptyTFM 0

instance Show (TermF (SharedTerm s)) where
  show FTermF{} = "termF fTermF"
  show _ = "termF SharedTerm"

-- | Return term for application using existing term in cache if it is avaiable.
getTerm :: AppCacheRef s -> TermF (SharedTerm s) -> IO (SharedTerm s)
getTerm r a =
  modifyMVar r $ \s -> do
    case lookupTFM a (acBindings s) of
      Just t -> return (s,t)
      Nothing -> do
          seq s' $ return (s',t)
        where t = STApp (acNextIdx s) a
              s' = s { acBindings = insertTFM a t (acBindings s)
                     , acNextIdx = acNextIdx s + 1
                     }

--------------------------------------------------------------------------------
-- Reduction to head-normal form

-- | Reduces beta-redexes, tuple/record selectors, and definition
-- equations at the top level of a term, and evaluates all arguments
-- to type constructors (including function, record, and tuple types).
scWhnf :: forall s. SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scWhnf sc = go []
  where
    go :: [Either (SharedTerm s) (Either Int FieldName)] -> SharedTerm s -> IO (SharedTerm s)
    go xs                     (asApp            -> Just (t, x)) = go (Left x : xs) t
    go xs                     (asTupleSelector  -> Just (t, i)) = go (Right (Left i) : xs) t
    go xs                     (asRecordSelector -> Just (t, n)) = go (Right (Right n) : xs) t
    go (Left x : xs)          (asLambda -> Just (_, _, body))   = instantiateVar sc 0 x body >>= go xs
    go (Right (Left i) : xs)  (asTupleValue -> Just ts)         = go xs (ts !! (i - 1))
    go (Right (Right i) : xs) (asRecordValue -> Just tm)        = go xs ((Map.!) tm i)
    go xs                     (asGlobalDef -> Just c)           = tryEqns c xs (maybe [] defEqs (findDef (scModule sc) c))
    go xs                     (asTupleType -> Just ts)          = do ts' <- mapM (scWhnf sc) ts
                                                                     t' <- scTupleType sc ts'
                                                                     foldM reapply t' xs
    go xs                     (asRecordType -> Just m)          = do m' <- T.mapM (scWhnf sc) m
                                                                     t' <- scRecordType sc m'
                                                                     foldM reapply t' xs
    go xs                     (asPi -> Just (x,aty,rty))        = do aty' <- scWhnf sc aty
                                                                     rty' <- scWhnf sc rty
                                                                     t' <- scPi sc x aty' rty'
                                                                     foldM reapply t' xs
    go xs                     (asDataType -> Just (c,args))     = do args' <- mapM (scWhnf sc) args
                                                                     t' <- scDataTypeApp sc c args'
                                                                     foldM reapply t' xs
    go xs                     t                                 = foldM reapply t xs

    reapply :: SharedTerm s -> Either (SharedTerm s) (Either Int FieldName) -> IO (SharedTerm s)
    reapply t (Left x) = scApply sc t x
    reapply t (Right (Left i)) = scTupleSelector sc t i
    reapply t (Right (Right i)) = scRecordSelect sc t i

    tryEqns :: Ident -> [Either (SharedTerm s) (Either Int FieldName)] -> [DefEqn Term] -> IO (SharedTerm s)
    tryEqns ident xs [] = scGlobalDef sc ident >>= flip (foldM reapply) xs
    tryEqns ident xs (DefEqn ps rhs : eqns) = do
      minst <- matchAll ps xs
      case minst of
        Just inst | and (zipWith (==) (Map.keys inst) [0..]) -> do
          rhs' <- scSharedTerm sc rhs
          t <- instantiateVarList sc 0 (reverse (Map.elems inst)) rhs'
          go (drop (length ps) xs) t
        _ -> tryEqns ident xs eqns

    matchAll :: [Pat Term] -> [Either (SharedTerm s) (Either Int FieldName)] -> IO (Maybe (Map Int (SharedTerm s)))
    matchAll [] _ = return $ Just Map.empty
    matchAll (_ : _) [] = return Nothing
    matchAll (_ : _) (Right _ : _) = return Nothing
    matchAll (p : ps) (Left x : xs) = do
      mm1 <- match p x
      case mm1 of
        Nothing -> return Nothing
        Just m1 -> do
          mm2 <- matchAll ps xs
          case mm2 of
            Nothing -> return Nothing
            Just m2 -> return $ Just (Map.union m1 m2)

    match :: Pat Term -> SharedTerm s -> IO (Maybe (Map Int (SharedTerm s)))
    match p x =
      case p of
        PVar _ i _  -> return $ Just (Map.singleton i x)
        PUnused _ _ -> return $ Just Map.empty
        PTuple ps   -> do v <- scWhnf sc x
                          case asTupleValue v of
                            Just xs | length xs == length ps -> matchAll ps (map Left xs)
                            _ -> return Nothing
        PRecord pm  -> do v <- scWhnf sc x
                          case asRecordValue v of
                            Just xm | Map.keys xm == Map.keys pm -> matchAll (Map.elems pm) (map Left $ Map.elems xm)
                            _ -> return Nothing
        PCtor i ps  -> do v <- scWhnf sc x
                          case asCtor v of
                            Just (s, xs) | i == s -> matchAll ps (map Left xs)
                            _ -> return Nothing

--------------------------------------------------------------------------------
-- Type checking

reducePi :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
reducePi sc t arg = do
  t' <- scWhnf sc t
  case asPi t' of
    Just (_, _, body) -> instantiateVar sc 0 arg body
    _                 -> fail "reducePi: not a Pi term"

scTypeOfGlobal :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfGlobal sc ident =
    case findDef (scModule sc) ident of
      Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
      Just d -> scSharedTerm sc (defType d)

scTypeOfDataType :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfDataType sc ident =
    case findDataType (scModule sc) ident of
      Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
      Just d -> scSharedTerm sc (dtType d)

scTypeOfCtor :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfCtor sc ident =
    case findCtor (scModule sc) ident of
      Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
      Just d -> scSharedTerm sc (ctorType d)

-- | Computes the type of a term as quickly as possible, assuming that
-- the term is well-typed.
scTypeOf :: forall s. SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scTypeOf sc t0 = scTypeOf' sc [] t0

-- | A version for open terms; the list argument encodes the type environment.
scTypeOf' :: forall s. SharedContext s -> [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
scTypeOf' sc env t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: SharedTerm s -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    memo (Unshared t) = termf t
    memo (STApp i t) = do
      table <- State.get
      case Map.lookup i table of
        Just x  -> return x
        Nothing -> do
          x <- termf t
          State.modify (Map.insert i x)
          return x
    sort :: SharedTerm s -> State.StateT (Map TermIndex (SharedTerm s)) IO Sort
    sort t = asSort =<< memo t
    termf :: TermF (SharedTerm s) -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    termf tf =
      case tf of
        FTermF ftf -> ftermf ftf
        App x y -> do
          tx <- memo x
          lift $ reducePi sc tx y
        Lambda name tp rhs -> do
          rtp <- lift $ scTypeOf' sc (tp : env) rhs
          lift $ scTermF sc (Pi name tp rtp)
        Pi _ tp rhs -> do
          ltp <- sort tp
          rtp <- asSort =<< lift (scTypeOf' sc (tp : env) rhs)
          lift $ scSort sc (max ltp rtp)
        Let defs rhs -> error "scTypeOf Let" defs rhs
        LocalVar i
          | i < length env -> lift $ incVars sc 0 (i + 1) (env !! i)
          | otherwise      -> fail $ "Dangling bound variable: " ++ show (i - length env)
        Constant _ t _ -> memo t
    ftermf :: FlatTermF (SharedTerm s)
           -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    ftermf tf =
      case tf of
        GlobalDef d -> lift $ scTypeOfGlobal sc d
        TupleValue l -> lift . scTupleType sc =<< traverse memo l
        TupleType l -> lift . scSort sc . maximum =<< traverse sort l
        TupleSelector t i -> do
          STApp _ (FTermF (TupleType ts)) <- memo t >>= liftIO . scWhnf sc
          return (ts !! (i-1)) -- FIXME test for i < length ts
        RecordValue m -> lift . scRecordType sc =<< traverse memo m
        RecordSelector t f -> do
          STApp _ (FTermF (RecordType m)) <- memo t >>= liftIO . scWhnf sc
          let Just tp = Map.lookup f m
          return tp
        RecordType m -> lift . scSort sc . maximum =<< traverse sort m
        CtorApp c args -> do
          t <- lift $ scTypeOfCtor sc c
          lift $ foldM (reducePi sc) t args
        DataTypeApp dt args -> do
          t <- lift $ scTypeOfDataType sc dt
          lift $ foldM (reducePi sc) t args
        Sort s -> lift $ scSort sc (sortOf s)
        NatLit _ -> lift $ scNatType sc
        ArrayValue tp vs -> lift $ do
          n <- scNat sc (fromIntegral (V.length vs))
          scFlatTermF sc (DataTypeApp preludeVecIdent [n, tp])
        FloatLit{}  -> lift $ scFlatTermF sc (DataTypeApp preludeFloatIdent  [])
        DoubleLit{} -> lift $ scFlatTermF sc (DataTypeApp preludeDoubleIdent [])
        StringLit{} -> lift $ scFlatTermF sc (DataTypeApp preludeStringIdent [])
        ExtCns ec   -> return $ ecType ec

asSort :: Monad m => SharedTerm s -> m Sort
asSort tp =
  case tp of
    Unshared (FTermF (Sort s)) -> return s
    STApp _ (FTermF (Sort s)) -> return s
    _ -> fail $ "Not a sort: " ++ show tp

alphaEquiv :: SharedTerm s -> SharedTerm s -> Bool
alphaEquiv = term
  where
    term (Unshared tf1) (Unshared tf2) = termf tf1 tf2
    term (Unshared tf1) (STApp _  tf2) = termf tf1 tf2
    term (STApp _  tf1) (Unshared tf2) = termf tf1 tf2
    term (STApp i1 tf1) (STApp i2 tf2) = i1 == i2 || termf tf1 tf2
    termf (FTermF ftf1) (FTermF ftf2) = ftermf ftf1 ftf2
    termf (App t1 u1) (App t2 u2) = term t1 t2 && term u1 u2
    termf (Lambda _ t1 u1) (Lambda _ t2 u2) = term t1 t2 && term u1 u2
    termf (Pi _ t1 u1) (Pi _ t2 u2) = term t1 t2 && term u1 u2
    termf (LocalVar i1) (LocalVar i2) = i1 == i2
    termf _ _ = False
    ftermf ftf1 ftf2 = case zipWithFlatTermF term ftf1 ftf2 of
                         Nothing -> False
                         Just ftf3 -> Data.Foldable.and ftf3

--------------------------------------------------------------------------------

-- | The inverse function to @scSharedTerm@.
unshare :: forall s. SharedTerm s -> Term
unshare t0 = State.evalState (go t0) Map.empty
  where
    go :: SharedTerm s -> State.State (Map TermIndex Term) Term
    go (Unshared t) = Term <$> traverse go t
    go (STApp i t) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          x <- Term <$> traverse go t
          State.modify (Map.insert i x)
          return x

instance Show (SharedTerm s) where
  show = show . unshare

scSharedTerm :: SharedContext s -> Term -> IO (SharedTerm s)
scSharedTerm sc = go
    where go (Term termf) = scTermF sc =<< traverse go termf

-- | Imports a term built in a different shared context into the given
-- shared context. The caller must ensure that all the global constants
-- appearing in the term are valid in the new context.
scImport :: forall s s'. SharedContext s -> SharedTerm s' -> IO (SharedTerm s)
scImport sc t0 =
    do cache <- newCache
       go cache t0
  where
    go :: Cache IORef TermIndex (SharedTerm s) -> SharedTerm s' -> IO (SharedTerm s)
    go cache (Unshared tf) = Unshared <$> traverse (go cache) tf
    go cache (STApp idx tf) = useCache cache idx (scTermF sc =<< traverse (go cache) tf)

--------------------------------------------------------------------------------

-- | Returns bitset containing indices of all free local variables.
looseVars :: forall s. SharedTerm s -> BitSet
looseVars t = State.evalState (go t) Map.empty
    where
      go :: SharedTerm s -> State.State (Map TermIndex BitSet) BitSet
      go (Unshared tf) = freesTermF <$> traverse go tf
      go (STApp i tf) = do
        memo <- State.get
        case Map.lookup i memo of
          Just x -> return x
          Nothing -> do
            x <- freesTermF <$> traverse go tf
            State.modify (Map.insert i x)
            return x

--------------------------------------------------------------------------------
-- Instantiating variables

instantiateVars :: forall s. SharedContext s
                -> (DeBruijnIndex -> Either (ExtCns (SharedTerm s)) DeBruijnIndex -> ChangeT IO (IO (SharedTerm s)))
                -> DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
instantiateVars sc f initialLevel t0 =
    do cache <- newCache
       let ?cache = cache in go initialLevel t0
  where
    go :: (?cache :: Cache IORef (TermIndex, DeBruijnIndex) (Change (SharedTerm s))) =>
          DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
    go l t@(Unshared tf) = preserveChangeT t (go' l tf)
    go l t@(STApp tidx tf) =
        ChangeT $ useCache ?cache (tidx, l) (runChangeT $ preserveChangeT t (go' l tf))

    go' :: (?cache :: Cache IORef (TermIndex, DeBruijnIndex) (Change (SharedTerm s))) =>
           DeBruijnIndex -> TermF (SharedTerm s) -> ChangeT IO (IO (SharedTerm s))
    go' l (FTermF (ExtCns ec)) = f l (Left ec)
    go' l (FTermF tf)       = scFlatTermF sc <$> (traverse (go l) tf)
    go' l (App x y)         = scTermF sc <$> (App <$> go l x <*> go l y)
    go' l (Lambda i tp rhs) = scTermF sc <$> (Lambda i <$> go l tp <*> go (l+1) rhs)
    go' l (Pi i lhs rhs)    = scTermF sc <$> (Pi i <$> go l lhs <*> go (l+1) rhs)
    go' l (Let defs r) = scTermF sc <$> (Let <$> changeList procDef defs <*> go l' r)
      where l' = l + length defs
            procDef :: LocalDef (SharedTerm s) -> ChangeT IO (LocalDef (SharedTerm s))
            procDef (Def sym tp eqs) = Def sym <$> go l tp <*> changeList procEq eqs
            procEq :: DefEqn (SharedTerm s) -> ChangeT IO (DefEqn (SharedTerm s))
            procEq (DefEqn pats rhs) = DefEqn pats <$> go eql rhs
              where eql = l' + sum (patBoundVarCount <$> pats)
    go' l (LocalVar i)
      | i < l     = pure $ scTermF sc (LocalVar i)
      | otherwise = f l (Right i)
    go' _ tf@(Constant _ _ _) = pure $ scTermF sc tf

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVarsChangeT :: SharedContext s
               -> DeBruijnIndex -> DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
incVarsChangeT sc initialLevel j
    | j == 0    = return
    | otherwise = instantiateVars sc fn initialLevel
    where
      fn _ (Left ec) = pure $ scFlatTermF sc $ ExtCns ec
      fn _ (Right i) = modified $ scTermF sc (LocalVar (i+j))

incVars :: SharedContext s
        -> DeBruijnIndex -> DeBruijnIndex -> SharedTerm s -> IO (SharedTerm s)
incVars sc i j t = commitChangeT (incVarsChangeT sc i j t)

-- | Substitute @t0@ for variable @k@ in @t@ and decrement all higher
-- dangling variables.
instantiateVarChangeT :: forall s. SharedContext s
                      -> DeBruijnIndex -> SharedTerm s -> SharedTerm s
                      -> ChangeT IO (SharedTerm s)
instantiateVarChangeT sc k t0 t =
    do cache <- newCache
       let ?cache = cache in instantiateVars sc fn 0 t
  where -- Use map reference to memoize instantiated versions of t.
        term :: (?cache :: Cache IORef DeBruijnIndex (SharedTerm s)) =>
                DeBruijnIndex -> ChangeT IO (SharedTerm s)
        term i = useCache ?cache i (incVarsChangeT sc 0 i t0)
        -- Instantiate variable 0.
        fn :: (?cache :: Cache IORef DeBruijnIndex (SharedTerm s)) =>
              DeBruijnIndex -> Either (ExtCns (SharedTerm s)) DeBruijnIndex -> ChangeT IO (IO (SharedTerm s))
        fn _ (Left ec) = pure $ scFlatTermF sc $ ExtCns ec
        fn i (Right j)
               | j  > i + k = modified $ scTermF sc (LocalVar (j - 1))
               | j == i + k = taint $ return <$> term i
               | otherwise  = pure $ scTermF sc (LocalVar j)

-- | Substitute @t0@ for variable @k@ in @t@ and decrement all higher
-- dangling variables.
instantiateVar :: SharedContext s
               -> DeBruijnIndex -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
instantiateVar sc k t0 t = commitChangeT (instantiateVarChangeT sc k t0 t)

-- | Substitute @ts@ for variables @[k .. k + length ts - 1]@ and
-- decrement all higher loose variables by @length ts@.
instantiateVarListChangeT :: forall s. SharedContext s
                          -> DeBruijnIndex -> [SharedTerm s]
                          -> SharedTerm s -> ChangeT IO (SharedTerm s)
instantiateVarListChangeT _ _ [] t = return t
instantiateVarListChangeT sc k ts t =
    do caches <- mapM (const newCache) ts
       instantiateVars sc (fn (zip caches ts)) 0 t
  where
    l = length ts
    -- Memoize instantiated versions of ts.
    term :: (Cache IORef DeBruijnIndex (SharedTerm s), SharedTerm s)
         -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
    term (cache, x) i = useCache cache i (incVarsChangeT sc 0 i x)
    -- Instantiate variables [k .. k+l-1].
    fn :: [(Cache IORef DeBruijnIndex (SharedTerm s), SharedTerm s)]
       -> DeBruijnIndex -> Either (ExtCns (SharedTerm s)) DeBruijnIndex -> ChangeT IO (IO (SharedTerm s))
    fn _ _ (Left ec) = pure $ scFlatTermF sc $ ExtCns ec
    fn rs i (Right j)
              | j >= i + k + l = modified $ scTermF sc (LocalVar (j - l))
              | j >= i + k     = taint $ return <$> term (rs !! (j - i - k)) i
              | otherwise      = pure $ scTermF sc (LocalVar j)

instantiateVarList :: SharedContext s
                   -> DeBruijnIndex -> [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
instantiateVarList sc k ts t = commitChangeT (instantiateVarListChangeT sc k ts t)

--------------------------------------------------------------------------------
-- Pretty printing

type SharedTermMap s v = StrictMap.Map (SharedTerm s) v

type OccurenceMap s = SharedTermMap s Word64

-- | Returns map that associated each term index appearing in the term
-- to the number of occurences in the shared term.
scTermCount :: SharedTerm s -> OccurenceMap s
scTermCount t0 = execState (rec [t0]) StrictMap.empty
  where rec :: [SharedTerm s] -> State (OccurenceMap s) ()
        rec [] = return ()
        rec (t:r) = do
          m <- get
          case StrictMap.lookup t m of
            Just n -> do
              put $ StrictMap.insert t (n+1) m
              rec r
            Nothing -> do
              when (looseVars t == 0) $ put (StrictMap.insert t 1 m)
              let (h,args) = asApplyAll t
              case unwrapTermF h of
                Constant _ _ _ -> rec (args ++ r)
                _ -> rec (Data.Foldable.foldr' (:) (args++r) (unwrapTermF h))
--              rec (Data.Foldable.foldr' (:) r (unwrapTermF t))

lineSep :: [Doc] -> Doc
lineSep l = hcat (punctuate line l)

scPrettyTermDoc :: forall s . SharedTerm s -> Doc
scPrettyTermDoc t0
    | null bound = ppt lcls0 PrecNone t0
    | otherwise =
        text "let { " <> nest 6 (lineSep lets) <$$>
        text "    }" <$$>
        text " in " <> align (ppt lcls0 PrecNone t0)
  where lcls0 = emptyLocalVarDoc
        cm = scTermCount t0 -- Occurence map
        -- Return true if variable should be introduced to name term.
        shouldName :: SharedTerm s -> Word64 -> Bool
        shouldName t c =
          case unwrapTermF t of
            FTermF GlobalDef{} -> False
            FTermF (TupleValue []) -> False
            FTermF (TupleType []) -> False
            FTermF (CtorApp _ []) -> False
            FTermF (DataTypeApp _ []) -> False
            FTermF NatLit{} -> False
            FTermF (ArrayValue _ v) | V.length v == 0 -> False
            FTermF FloatLit{} -> False
            FTermF DoubleLit{} -> False
            FTermF ExtCns{} -> False
            LocalVar{} -> False
            _ -> c > 1

        -- Terms bound in map.
        bound :: [SharedTerm s]
        bound = [ t | (t,c) <- Map.toList cm, shouldName t c ]

        var :: Word64 -> Doc
        var n = char 'x' <> integer (toInteger n)

        lets = [ var n <+> char '=' <+> ppTermF ppt lcls0 PrecNone (unwrapTermF t) <> char ';'
               | (t,n) <- bound `zip` [0..]
               ]

        dm :: SharedTermMap s Doc
        dm = Data.Foldable.foldl' insVar StrictMap.empty (bound `zip` [0..])
          where insVar m (t,n) = StrictMap.insert t (var n) m

        ppt :: LocalVarDoc -> Prec -> SharedTerm s -> Doc
        ppt lcls p t =
          case StrictMap.lookup t dm of
            Just d -> d
            Nothing -> ppTermF ppt lcls p (unwrapTermF t)

scPrettyTerm :: SharedTerm s -> String
scPrettyTerm t = show (scPrettyTermDoc t)

--------------------------------------------------------------------------------
-- Building shared terms

scApplyAll :: SharedContext s -> SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scApplyAll sc = foldlM (scApply sc)

-- | Returns the defined constant with the given name. Fails if no
-- such constant exists in the module.
scLookupDef :: SharedContext s -> Ident -> IO (SharedTerm s)
scLookupDef sc ident = scGlobalDef sc ident --FIXME: implement module check.

-- | Deprecated. Use scGlobalDef or scLookupDef instead.
scDefTerm :: SharedContext s -> TypedDef -> IO (SharedTerm s)
scDefTerm sc d = scGlobalDef sc (defIdent d)

-- TODO: implement version of scCtorApp that looks up the arity of the
-- constructor identifier in the module.

-- | Deprecated. Use scCtorApp instead.
scApplyCtor :: SharedContext s -> TypedCtor -> [SharedTerm s] -> IO (SharedTerm s)
scApplyCtor sc c args = scCtorApp sc (ctorName c) args

scSort :: SharedContext s -> Sort -> IO (SharedTerm s)
scSort sc s = scFlatTermF sc (Sort s)

scNat :: SharedContext s -> Nat -> IO (SharedTerm s)
scNat sc n = scFlatTermF sc (NatLit (toInteger n))

scString :: SharedContext s -> String -> IO (SharedTerm s)
scString sc s = scFlatTermF sc (StringLit s)

scVector :: SharedContext s -> SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scVector sc e xs = scFlatTermF sc (ArrayValue e (V.fromList xs))

scRecord :: SharedContext s -> Map FieldName (SharedTerm s) -> IO (SharedTerm s)
scRecord sc m = scFlatTermF sc (RecordValue m)

scRecordSelect :: SharedContext s -> SharedTerm s -> FieldName -> IO (SharedTerm s)
scRecordSelect sc t fname = scFlatTermF sc (RecordSelector t fname)

scRecordType :: SharedContext s -> Map FieldName (SharedTerm s) -> IO (SharedTerm s)
scRecordType sc m = scFlatTermF sc (RecordType m)

scTuple :: SharedContext s -> [SharedTerm s] -> IO (SharedTerm s)
scTuple sc ts = scFlatTermF sc (TupleValue ts)

scTupleType :: SharedContext s -> [SharedTerm s] -> IO (SharedTerm s)
scTupleType sc ts = scFlatTermF sc (TupleType ts)

scTupleSelector :: SharedContext s -> SharedTerm s -> Int -> IO (SharedTerm s)
scTupleSelector sc t i = scFlatTermF sc (TupleSelector t i)

scFun :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scFun sc a b = do b' <- incVars sc 0 1 b
                  scTermF sc (Pi "_" a b')

scFunAll :: SharedContext s
         -> [SharedTerm s]
         -> SharedTerm s
         -> IO (SharedTerm s)
scFunAll sc argTypes resultType = foldrM (scFun sc) resultType argTypes

scLambda :: SharedContext s
         -> String
         -> SharedTerm s
         -> SharedTerm s
         -> IO (SharedTerm s)
scLambda sc varname ty body = scTermF sc (Lambda varname ty body)

scLambdaList :: SharedContext s
             -> [(String, SharedTerm s)]
             -> SharedTerm s
             -> IO (SharedTerm s)
scLambdaList _ [] rhs = return rhs
scLambdaList sc ((nm,tp):r) rhs =
  scLambda sc nm tp =<< scLambdaList sc r rhs

scPi :: SharedContext s
     -> String
     -> SharedTerm s
     -> SharedTerm s
     -> IO (SharedTerm s)
scPi sc nm tp body = scTermF sc (Pi nm tp body)

scPiList :: SharedContext s
             -> [(String, SharedTerm s)]
             -> SharedTerm s
             -> IO (SharedTerm s)
scPiList _ [] rhs = return rhs
scPiList sc ((nm,tp):r) rhs = scPi sc nm tp =<< scPiList sc r rhs

scLocalVar :: SharedContext s
           -> DeBruijnIndex
           -> IO (SharedTerm s)
scLocalVar sc i = scTermF sc (LocalVar i)

scGlobalApply :: SharedContext s -> Ident -> [SharedTerm s] -> IO (SharedTerm s)
scGlobalApply sc i ts =
    do c <- scGlobalDef sc i
       scApplyAll sc c ts

------------------------------------------------------------
-- Building terms using prelude functions

scBool :: SharedContext s -> Bool -> IO (SharedTerm s)
scBool sc True  = scCtorApp sc "Prelude.True" []
scBool sc False = scCtorApp sc "Prelude.False" []

scBoolType :: SharedContext s -> IO (SharedTerm s)
scBoolType sc = scDataTypeApp sc "Prelude.Bool" []

scNatType :: SharedContext s -> IO (SharedTerm s)
scNatType sc = scDataTypeApp sc preludeNatIdent []

scVecType :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scVecType sc n e = scDataTypeApp sc "Prelude.Vec" [n, e]

scNot :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scNot sc t = scGlobalApply sc "Prelude.not" [t]

scAnd :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scAnd sc x y = scGlobalApply sc "Prelude.and" [x,y]

scOr :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scOr sc x y = scGlobalApply sc "Prelude.or" [x,y]

scXor :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scXor sc x y = scGlobalApply sc "Prelude.xor" [x,y]

scBoolEq :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBoolEq sc x y = scGlobalApply sc "Prelude.boolEq" [x,y]

-- ite :: (a :: sort 1) -> Bool -> a -> a -> a;
scIte :: SharedContext s -> SharedTerm s -> SharedTerm s ->
         SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scIte sc t b x y = scGlobalApply sc "Prelude.ite" [t, b, x, y]

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
scAppend :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s ->
            SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scAppend sc t m n x y = scGlobalApply sc "Prelude.append" [m, n, t, x, y]

-- | slice :: (e :: sort 1) -> (i n o :: Nat) -> Vec (addNat (addNat i n) o) e -> Vec n e;
scSlice :: SharedContext s -> SharedTerm s -> SharedTerm s ->
           SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scSlice sc e i n o a = scGlobalApply sc "Prelude.slice" [e, i, n, o, a]

-- | get :: (n :: Nat) -> (e :: sort 0) -> Vec n e -> Fin n -> e;
scGet :: SharedContext s -> SharedTerm s -> SharedTerm s ->
         SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scGet sc n e v i = scGlobalApply sc (mkIdent preludeName "get") [n, e, v, i]

-- | bvAt :: (n :: Nat) -> (a :: sort 0) -> (i :: Nat) -> Vec n a -> bitvector i -> a;
scBvAt :: SharedContext s -> SharedTerm s -> SharedTerm s ->
         SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvAt sc n a i xs idx = scGlobalApply sc (mkIdent preludeName "bvAt") [n, a, i, xs, idx]

-- | at :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a;
scAt :: SharedContext s -> SharedTerm s -> SharedTerm s ->
        SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scAt sc n a xs idx = scGlobalApply sc (mkIdent preludeName "at") [n, a, xs, idx]

-- | single :: (e :: sort 1) -> e -> Vec 1 e;
-- single e x = generate 1 e (\(i :: Fin 1) -> x);
scSingle :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scSingle sc e x = scGlobalApply sc (mkIdent preludeName "single") [e, x]

-- Primitive operations on nats

scAddNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scAddNat sc x y = scGlobalApply sc "Prelude.addNat" [x,y]

scSubNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scSubNat sc x y = scGlobalApply sc "Prelude.subNat" [x,y]

scMulNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scMulNat sc x y = scGlobalApply sc "Prelude.mulNat" [x,y]

scEqualNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scEqualNat sc x y = scGlobalApply sc "Prelude.equalNat" [x,y]

scLtNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scLtNat sc x y = scGlobalApply sc "Prelude.ltNat" [x,y]

-- Primitive operations on bitvectors

-- | bitvector :: (n : Nat) -> sort 1
-- bitvector n = Vec n Bool
scBitvector :: SharedContext s -> Nat -> IO (SharedTerm s)
scBitvector sc size = do
  c <- scGlobalDef sc "Prelude.bitvector"
  s <- scNat sc size
  scApply sc c s

-- | bvNat :: (x :: Nat) -> Nat -> bitvector x;
scBvNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvNat sc x y = scGlobalApply sc "Prelude.bvNat" [x, y]

-- bvToNat :: (n :: Nat) -> bitvector n -> Nat;
scBvToNat :: SharedContext s -> Nat -> SharedTerm s -> IO (SharedTerm s)
scBvToNat sc n x = do
    n' <- scNat sc n
    scGlobalApply sc "Prelude.bvToNat" [n',x]

-- | Returns constant bitvector.
scBvConst :: SharedContext s -> Nat -> Integer -> IO (SharedTerm s)
scBvConst sc w v = assert (w <= fromIntegral (maxBound :: Int)) $ do
  x <- scNat sc w
  y <- scNat sc $ fromInteger $ v .&. (1 `shiftL` fromIntegral w - 1)
  scGlobalApply sc "Prelude.bvNat" [x, y]

-- | FinVal :: (x r :: Nat) -> Fin (Succ (addNat r x));
scFinVal :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scFinVal sc a b = scCtorApp sc "Prelude.FinVal" [a, b]

-- | bvNeg :: (x::Nat) -> bitvector x -> bitvector x;
scBvNeg :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvNeg sc n x = scGlobalApply sc "Prelude.bvNeg" [n, x]

-- | bvAdd/Sub/Mul :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
scBvAdd, scBvSub, scBvMul, scBvURem, scBvUDiv, scBvSRem, scBvSDiv
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvAdd sc n x y = scGlobalApply sc "Prelude.bvAdd" [n, x, y]
scBvSub sc n x y = scGlobalApply sc "Prelude.bvSub" [n, x, y]
scBvMul sc n x y = scGlobalApply sc "Prelude.bvMul" [n, x, y]
scBvURem sc n x y = scGlobalApply sc "Prelude.bvURem" [n, x, y]
scBvUDiv sc n x y = scGlobalApply sc "Prelude.bvUDiv" [n, x, y]
scBvSRem sc n x y = scGlobalApply sc "Prelude.bvSRem" [n, x, y]
scBvSDiv sc n x y = scGlobalApply sc "Prelude.bvSDiv" [n, x, y]

-- | bvOr/And/Xor :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n;
scBvOr, scBvAnd, scBvXor
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvAnd sc n x y = scGlobalApply sc "Prelude.bvAnd" [n, x, y]
scBvXor sc n x y = scGlobalApply sc "Prelude.bvXor" [n, x, y]
scBvOr  sc n x y = scGlobalApply sc "Prelude.bvOr"  [n, x, y]

-- | bvNot :: (n :: Nat) -> bitvector n -> bitvector n;
scBvNot :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvNot sc n x = scGlobalApply sc "Prelude.bvNot" [n, x]

-- | bvEq :: (n :: Nat) -> bitvector n -> bitvector n -> Bool;
scBvEq, scBvUGe, scBvUGt, scBvULe, scBvULt
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvEq  sc n x y = scGlobalApply sc "Prelude.bvEq"  [n, x, y]
scBvUGe sc n x y = scGlobalApply sc "Prelude.bvuge" [n, x, y]
scBvULe sc n x y = scGlobalApply sc "Prelude.bvule" [n, x, y]
scBvUGt sc n x y = scGlobalApply sc "Prelude.bvugt" [n, x, y]
scBvULt sc n x y = scGlobalApply sc "Prelude.bvult" [n, x, y]


-- | bvsgt/bvsge/bvslt/bvsle :: (n :: Nat) -> bitvector n -> bitvector n -> Bool;
scBvSGt, scBvSGe, scBvSLt, scBvSLe
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvSGe sc n x y = scGlobalApply sc "Prelude.bvsge" [n, x, y]
scBvSLe sc n x y = scGlobalApply sc "Prelude.bvsle" [n, x, y]
scBvSGt sc n x y = scGlobalApply sc "Prelude.bvsgt" [n, x, y]
scBvSLt sc n x y = scGlobalApply sc "Prelude.bvslt" [n, x, y]

-- | bvShl, bvShr :: (n :: Nat) -> bitvector n -> Nat -> bitvector n;
scBvShl, scBvShr
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvShl sc n x y = scGlobalApply sc "Prelude.bvShl" [n, x, y]
scBvShr sc n x y = scGlobalApply sc "Prelude.bvShr" [n, x, y]

-- | bvSShr :: (w :: Nat) -> bitvector (Succ w) -> Nat -> bitvector (Succ w);
scBvSShr :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvSShr sc n x y = scGlobalApply sc "Prelude.bvSShr" [n, x, y]

-- | bvUExt :: (x y :: Nat) -> bitvector y -> bitvector (addNat x y);
scBvUExt :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvUExt sc n m x = scGlobalApply sc "Prelude.bvUExt" [n,m,x]

-- | bvSExt :: (x y :: Nat) -> bitvector (Succ y) -> bitvector (addNat x (Succ y));
scBvSExt :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvSExt sc n m x = scGlobalApply sc "Prelude.bvSExt" [n,m,x]

-- | bvTrunc :: (x y :: Nat) -> bitvector (addNat x y) -> bitvector y;
scBvTrunc :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvTrunc sc n m x = scGlobalApply sc "Prelude.bvTrunc" [n,m,x]

------------------------------------------------------------
-- | The default instance of the SharedContext operations.
mkSharedContext :: Module -> IO (SharedContext s)
mkSharedContext m = do
  vr <- newMVar 0 -- Reference for getting variables.
  cr <- newMVar emptyAppCache
  let freshGlobalVar = modifyMVar vr (\i -> return (i+1, i))
  return SharedContext {
             scModule = m
           , scTermF = getTerm cr
           , scFreshGlobalVar = freshGlobalVar
           }

useChangeCache :: MonadRef r m => Cache r k (Change v) -> k -> ChangeT m v -> ChangeT m v
useChangeCache c k a = ChangeT $ useCache c k (runChangeT a)

-- | Performs an action when a value has been modified, and otherwise
-- returns a pure value.
whenModified :: (Functor m, Monad m) => b -> (a -> m b) -> ChangeT m a -> ChangeT m b
whenModified b f m = ChangeT $ do
  ca <- runChangeT m
  case ca of
    Original{} -> return (Original b)
    Modified a -> Modified <$> f a

extIdx :: SharedTerm s -> Maybe VarIndex
extIdx (unwrapTermF -> FTermF (ExtCns ec)) = Just (ecVarIndex ec)
extIdx _ = Nothing

extName :: SharedTerm s -> Maybe String
extName (unwrapTermF -> FTermF (ExtCns ec)) = Just (ecName ec)
extName _ = Nothing

-- | Return a list of all ExtCns subterms in the given term, sorted by
-- index. Does not traverse the unfoldings of @Constant@ terms.
getAllExts :: SharedTerm s -> [SharedTerm s]
getAllExts t = sortBy (comparing extIdx) $ Set.toList args
    where (seen, exts) = getExtCns (Set.empty, Set.empty) t
          tf = unwrapTermF t
          args = snd $ foldl' getExtCns (seen, exts) tf
          getExtCns acc@(is, _) (STApp idx _) | Set.member idx is = acc
          getExtCns (is, a) t'@(STApp idx (FTermF (ExtCns _))) =
            (Set.insert idx is, Set.insert t' a)
          getExtCns (is, a) t'@(Unshared (FTermF (ExtCns _))) =
            (is, Set.insert t' a)
          getExtCns acc (STApp _ (Constant _ _ _)) = acc
          getExtCns acc (Unshared (Constant _ _ _)) = acc
          getExtCns (is, a) (STApp idx tf') =
            foldl' getExtCns (Set.insert idx is, a) tf'
          getExtCns acc (Unshared tf') =
            foldl' getExtCns acc tf'

-- | Instantiate some of the external constants
scInstantiateExt :: forall s
                  . SharedContext s
                 -> Map VarIndex (SharedTerm s)
                 -> SharedTerm s
                 -> IO (SharedTerm s)
scInstantiateExt sc vmap = commitChangeT . instantiateVars sc fn 0
  where fn l (Left ec) =
            case Map.lookup (ecVarIndex ec) vmap of
               Just t  -> modified $ incVars sc 0 l t
               Nothing -> pure $ scFlatTermF sc $ ExtCns ec
        fn _ (Right i) = pure $ scTermF sc $ LocalVar i

{-
-- RWD: I'm pretty sure the following implementation gets incorrect results when
-- the terms being substituted have free deBruijn variables.  The above is a
-- reimplementation based on instantiateVars that does the necessary deBruijn
-- shifting.

scInstantiateExt sc vmap t0 = do
  tcache <- newCacheMap' Map.empty
  let go :: SharedTerm s -> ChangeT IO (SharedTerm s)
      go t@(Unshared tf) =
        case tf of
          -- | Lookup variable in term if it is bound.
          FTermF (ExtCns ec) ->
            maybe (return t) modified $ Map.lookup (ecVarIndex ec) vmap
          -- | Recurse on other terms.
          _ -> whenModified t (scTermF sc) (traverse go tf)
      go t@(STApp idx tf) =
        case tf of
          -- Lookup variable in term if it is bound.
          FTermF (ExtCns ec) ->
            maybe (return t) modified $ Map.lookup (ecVarIndex ec) vmap
          -- Recurse on other terms.
          _ -> useChangeCache tcache idx $
                 whenModified t (scTermF sc) (traverse go tf)
  commitChangeT (go t0)
-}

-- | Abstract over the given list of external constants by wrapping the given term with
--   lambdas and replacing the external constant occurences with the appropriate local variables
scAbstractExts :: forall s. SharedContext s -> [ExtCns (SharedTerm s)] -> SharedTerm s -> IO (SharedTerm s)
scAbstractExts _ [] x = return x
scAbstractExts sc exts x =
   do ls <- sequence [ scTermF sc (LocalVar db) >>= \t -> return ( ecVarIndex ec, t )
                     | ec <- reverse exts
                     | db <- [0 .. ]
                     ]
      let m = Map.fromList ls
      let lams = [ ( ecName ec, ecType ec ) | ec <- exts ]
      scLambdaList sc lams =<< scInstantiateExt sc m x


scUnfoldConstants :: forall s. SharedContext s -> [Ident] -> SharedTerm s -> IO (SharedTerm s)
scUnfoldConstants sc ids t0 = do
  cache <- newCache
  let go :: SharedTerm s -> IO (SharedTerm s)
      go t@(Unshared tf) =
        case tf of
          Constant ident rhs _
            | ident `elem` ids -> go rhs
            | otherwise        -> return t
          _ -> Unshared <$> traverse go tf
      go t@(STApp idx tf) = useCache cache idx $
        case tf of
          Constant ident rhs _
            | ident `elem` ids -> go rhs
            | otherwise        -> return t
          _ -> scTermF sc =<< traverse go tf
  go t0

-- | TODO: test whether this version is slower or faster.
scUnfoldConstants' :: forall s. SharedContext s -> [Ident] -> SharedTerm s -> IO (SharedTerm s)
scUnfoldConstants' sc ids t0 = do
  tcache <- newCacheMap' Map.empty
  let go :: SharedTerm s -> ChangeT IO (SharedTerm s)
      go t@(Unshared tf) =
        case tf of
          Constant ident rhs _
            | ident `elem` ids -> taint (go rhs)
            | otherwise        -> pure t
          _ -> whenModified t (return . Unshared) (traverse go tf)
      go t@(STApp idx tf) =
        case tf of
          Constant ident rhs _
            | ident `elem` ids -> taint (go rhs)
            | otherwise        -> pure t
          _ -> useChangeCache tcache idx $
                 whenModified t (scTermF sc) (traverse go tf)
  commitChangeT (go t0)

-- | Return the number of DAG nodes used by the given @SharedTerm@.
scSharedSize :: SharedTerm s -> Integer
scSharedSize = fst . go (0, Set.empty)
  where
    go (sz, seen) (Unshared tf) = foldl' go (strictPair (sz + 1) seen) tf
    go (sz, seen) (STApp idx tf)
      | Set.member idx seen = (sz, seen)
      | otherwise = foldl' go (strictPair (sz + 1) (Set.insert idx seen)) tf

strictPair :: a -> b -> (a, b)
strictPair x y = x `seq` y `seq` (x, y)

-- | Return the number of nodes that would be used by the given
-- @SharedTerm@ if it were represented as a tree instead of a DAG.
scTreeSize :: SharedTerm s -> Integer
scTreeSize = fst . go (0, Map.empty)
  where
    go (sz, seen) (Unshared tf) = foldl' go (sz + 1, seen) tf
    go (sz, seen) (STApp idx tf) =
      case Map.lookup idx seen of
        Just sz' -> (sz + sz', seen)
        Nothing -> (sz + sz', Map.insert idx sz' seen')
          where (sz', seen') = foldl' go (1, seen) tf
