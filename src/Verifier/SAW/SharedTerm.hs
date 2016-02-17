{-# LANGUAGE BangPatterns #-}
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
Copyright   : Galois, Inc. 2012-2015
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
  , smallestFreeVar
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
  , scMinNat
  , scMaxNat

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
  , scUnitValue
  , scUnitType
  , scPairValue
  , scPairType
  , scPairLeft
  , scPairRight
  , scEmptyValue
  , scEmptyType
  , scFieldValue
  , scFieldType
  , scTuple
  , scTupleType
  , scTupleSelector
  , scVector
  , scVecType
  , scUpdNatFun
  , scUpdBvFun
  , scTermCount
  , scPrettyTerm
  , scPrettyTermDoc
  , scGlobalApply
  , scSharedTerm
  , scImport
    -- ** Normalization
  , scWhnf
  , scConvertable
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
  , scImplies
  , scXor
  , scBoolEq
  , scIte
  , scSingle
  , scSlice
  -- *** Integer primitives
  , scInteger
  , scIntAdd, scIntSub, scIntMul
  , scIntDiv, scIntMod, scIntNeg
  , scIntMin, scIntMax
  , scIntEq, scIntLe, scIntLt
  , scIntToNat, scNatToInt
  , scIntToBv, scBvToInt, scSbvToInt

    -- *** Bitvector primitives
  , scBitvector
  , scBvNat
  , scBvToNat
  , scBvAt
  , scBvConst
  , scFinVal
  , scBvNonzero, scBvBool
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
   , scOpenTerm
   , scCloseTerm
    -- ** Variable substitution
  , instantiateVar
  , instantiateVarList
  , betaNormalize
  , getAllExts
  , getAllExtSet
  , getConstantSet
  , scInstantiateExt
  , scAbstractExts
  , incVars
  , scUnfoldConstants
  , scUnfoldConstants'
  , scUnfoldConstantSet
  , scUnfoldConstantSet'
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
import qualified Data.Foldable as Fold
import Data.Foldable (foldl', foldlM, foldrM)
import Data.Hashable (Hashable(..))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IORef (IORef)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Typeable
import qualified Data.Vector as V
import Data.Word
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.Recognizer
import Verifier.SAW.TypedAST hiding (incVars, instantiateVarList)
import qualified Verifier.SAW.TermNet as Net

#if !MIN_VERSION_base(4,8,0)
countTrailingZeros :: (FiniteBits b) => b -> Int
countTrailingZeros x = go 0
  where
    go i | i >= w      = i
         | testBit x i = i
         | otherwise   = go (i+1)
    w = finiteBitSize x
#endif

newtype Uninterp s = Uninterp { getUninterp :: (String, SharedTerm s) } deriving Show

type TermIndex = Int -- Word64

data SharedTerm s
  = STApp
     { stAppIndex    :: {-# UNPACK #-} !TermIndex
     , stAppFreeVars :: !BitSet -- Free variables
     , stAppTermF    :: !(TermF (SharedTerm s))
     }
  | Unshared !(TermF (SharedTerm s))
  deriving (Typeable)

instance Hashable (SharedTerm s) where
  hashWithSalt salt STApp{ stAppIndex = i } = salt `combine` 0x00000000 `hashWithSalt` hash i
  hashWithSalt salt (Unshared t) = salt `combine` 0x55555555 `hashWithSalt` hash t

-- | Combine two given hash values.  'combine' has zero as a left
-- identity. (FNV hash, copied from Data.Hashable 1.2.1.0.)
combine :: Int -> Int -> Int
combine h1 h2 = (h1 * 0x01000193) `xor` h2

instance Termlike (SharedTerm s) where
  unwrapTermF STApp{ stAppTermF = tf} = tf
  unwrapTermF (Unshared tf) = tf

instance Eq (SharedTerm s) where
  (==) = alphaEquiv

instance Ord (SharedTerm s) where
  compare (STApp{ stAppIndex = i}) (STApp{ stAppIndex = j}) | i == j = EQ
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
    App (STApp{ stAppIndex = i }) (STApp{ stAppIndex = j}) ->
      IntMap.lookup i (appMapTFM tfm) >>= IntMap.lookup j
    _ -> HMap.lookup tf (hashMapTFM tfm)

insertTFM :: TermF (SharedTerm s) -> a -> TermFMap s a -> TermFMap s a
insertTFM tf x tfm =
  case tf of
    App (STApp{ stAppIndex = i }) (STApp{ stAppIndex = j}) ->
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
        where t = STApp{ stAppIndex = acNextIdx s
                       , stAppFreeVars = freesTermF (fmap looseVars a)
                       , stAppTermF = a
                       }
              s' = s { acBindings = insertTFM a t (acBindings s)
                     , acNextIdx = acNextIdx s + 1
                     }

--------------------------------------------------------------------------------
-- Reduction to head-normal form

-- | Reduces beta-redexes, tuple/record selectors, and definition
-- equations at the top level of a term, and evaluates all arguments
-- to type constructors (including function, record, and tuple types).
scWhnf :: forall s. SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scWhnf sc t0 =
  do cache <- newCacheIntMap
     let ?cache = cache in memo t0
  where
    memo :: (?cache :: Cache IORef TermIndex (SharedTerm s)) => SharedTerm s -> IO (SharedTerm s)
    memo t =
      case t of
        Unshared _ -> go [] t
        STApp { stAppIndex = i } -> useCache ?cache i (go [] t)

    go :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
          [Either (SharedTerm s) (Either Bool FieldName)] -> SharedTerm s -> IO (SharedTerm s)
    go xs                     (asApp            -> Just (t, x)) = go (Left x : xs) t
    go xs                     (asPairSelector   -> Just (t, i)) = go (Right (Left i) : xs) t
    go xs                     (asRecordSelector -> Just (t, n)) = go (Right (Right n) : xs) t
    go (Left x : xs)          (asLambda -> Just (_, _, body))   = instantiateVar sc 0 x body >>= go xs
    go (Right (Left i) : xs)  (asPairValue -> Just (a, b))      = go xs (if i then b else a)
    go (Right (Right i) : xs) (asFieldValue -> Just (s, a, b))  = do s' <- memo s
                                                                     b' <- memo b
                                                                     t' <- scFieldValue sc s' a b'
                                                                     case asRecordValue t' of
                                                                       Just tm -> go xs ((Map.!) tm i)
                                                                       Nothing -> foldM reapply t' xs
    go xs                     (asGlobalDef -> Just c)           = tryEqns c xs (maybe [] defEqs (findDef (scModule sc) c))
    go xs                     (asPairValue -> Just (a, b))      = do b' <- memo b
                                                                     t' <- scPairValue sc a b'
                                                                     foldM reapply t' xs
    go xs                     (asFieldValue -> Just (s, a, b))  = do s' <- memo s
                                                                     b' <- memo b
                                                                     t' <- scFieldValue sc s' a b'
                                                                     foldM reapply t' xs
    go xs                     (asPairType -> Just (a, b))       = do a' <- memo a
                                                                     b' <- memo b
                                                                     t' <- scPairType sc a' b'
                                                                     foldM reapply t' xs
    go xs                     (asFieldType -> Just (s, a, b))   = do s' <- memo s
                                                                     a' <- memo a
                                                                     b' <- memo b
                                                                     t' <- scFieldType sc s' a' b'
                                                                     foldM reapply t' xs
    go xs                     (asPi -> Just (x,aty,rty))        = do aty' <- memo aty
                                                                     rty' <- memo rty
                                                                     t' <- scPi sc x aty' rty'
                                                                     foldM reapply t' xs
    go xs                     (asDataType -> Just (c,args))     = do args' <- mapM memo args
                                                                     t' <- scDataTypeApp sc c args'
                                                                     foldM reapply t' xs
    -- FIXME? what about Let?
    go xs                     t                                 = foldM reapply t xs

    reapply :: SharedTerm s -> Either (SharedTerm s) (Either Bool FieldName) -> IO (SharedTerm s)
    reapply t (Left x) = scApply sc t x
    reapply t (Right (Left i)) = scPairSelector sc t i
    reapply t (Right (Right i)) = scRecordSelect sc t i

    tryEqns :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
               Ident -> [Either (SharedTerm s) (Either Bool FieldName)] -> [DefEqn Term] -> IO (SharedTerm s)
    tryEqns ident xs [] = scGlobalDef sc ident >>= flip (foldM reapply) xs
    tryEqns ident xs (DefEqn ps rhs : eqns) = do
      minst <- matchAll ps xs
      case minst of
        Just inst | and (zipWith (==) (Map.keys inst) [0..]) -> do
          rhs' <- scSharedTerm sc rhs
          t <- instantiateVarList sc 0 (reverse (Map.elems inst)) rhs'
          go (drop (length ps) xs) t
        _ -> tryEqns ident xs eqns

    matchAll :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
                [Pat Term] -> [Either (SharedTerm s) (Either Bool FieldName)]
                  -> IO (Maybe (Map Int (SharedTerm s)))
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

    match :: (?cache :: Cache IORef TermIndex (SharedTerm s)) =>
             Pat Term -> SharedTerm s -> IO (Maybe (Map Int (SharedTerm s)))
    match p x =
      case p of
        PVar _ i _  -> return $ Just (Map.singleton i x)
        PUnused _ _ -> return $ Just Map.empty
        PUnit       -> do v <- memo x
                          case asTupleValue v of
                            Just [] -> matchAll [] []
                            _ -> return Nothing
        PPair p1 p2 -> do v <- memo x
                          case asPairValue v of
                            Just (v1, v2) -> matchAll [p1, p2] [Left v1, Left v2]
                            _ -> return Nothing
        PEmpty      -> do v <- memo x
                          case asFTermF v of
                            Just EmptyValue -> return $ Just Map.empty
                            _ -> return Nothing
        PField p1 p2 p3 -> do v <- memo x
                              case asFTermF v of
                                Just (FieldValue v1 v2 v3) ->
                                  matchAll [p1, p2, p3] [Left v1, Left v2, Left v3]
                                _ -> return Nothing
        PCtor i ps  -> do v <- memo x
                          case asCtor v of
                            Just (s, xs) | i == s -> matchAll ps (map Left xs)
                            _ -> return Nothing
        PString s   -> do v <- memo x
                          case asStringLit v of
                            Just s' | s == s' -> matchAll [] []
                            _ -> return Nothing


-- | Test if two terms are convertable; that is, if they are equivalant under evaluation.
scConvertable :: forall s. SharedContext s
              -> Bool -- ^ Should abstract constants be unfolded during this check?
              -> SharedTerm s
              -> SharedTerm s
              -> IO Bool
scConvertable sc unfoldConst tm1 tm2 = do
   c <- newCache
   go c tm1 tm2

 where whnf :: Cache IORef TermIndex (SharedTerm s) -> SharedTerm s -> IO (TermF (SharedTerm s))
       whnf _c t@(Unshared _) = unwrapTermF <$> scWhnf sc t
       whnf c t@(STApp{ stAppIndex = idx}) = unwrapTermF <$> (useCache c idx $ scWhnf sc t)

       go :: Cache IORef TermIndex (SharedTerm s) -> SharedTerm s -> SharedTerm s -> IO Bool
       go _c (STApp{ stAppIndex = idx1}) (STApp{ stAppIndex = idx2})
           | idx1 == idx2 = return True   -- succeed early case
       go c t1 t2 = join (goF c <$> whnf c t1 <*> whnf c t2)

       goF :: Cache IORef TermIndex (SharedTerm s) -> TermF (SharedTerm s) -> TermF (SharedTerm s) -> IO Bool

       goF c (Constant _ _ x) y | unfoldConst = join (goF c <$> whnf c x <*> return y)
       goF c x (Constant _ _ y) | unfoldConst = join (goF c <$> return x <*> whnf c y)

       goF c (FTermF ftf1) (FTermF ftf2) =
               case zipWithFlatTermF (go c) ftf1 ftf2 of
                 Nothing -> return False
                 Just zipped -> Fold.and <$> traverse id zipped

       goF _c (LocalVar i) (LocalVar j) = return (i == j)

       goF c (App f1 x1) (App f2 x2) =
              pure (&&) <*> go c f1 f2 <*> go c x1 x2

       goF c (Lambda _ ty1 body1) (Lambda _ ty2 body2) =
              pure (&&) <*> go c ty1 ty2 <*> go c body1 body2

       goF c (Pi _ ty1 body1) (Pi _ ty2 body2) =
              pure (&&) <*> go c ty1 ty2 <*> go c body1 body2

       -- FIXME? what about Let?

       -- final catch-all case
       goF _c x y = return $ alphaEquiv (Unshared x) (Unshared y)

--------------------------------------------------------------------------------
-- Type checking

reducePi :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
reducePi sc t arg = do
  t' <- scWhnf sc t
  case asPi t' of
    Just (_, _, body) -> instantiateVar sc 0 arg body
    _                 -> fail $ unlines ["reducePi: not a Pi term", show t']

scTypeOfGlobal :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfGlobal sc ident =
    case findDef (scModule sc) ident of
      Nothing -> fail $ "scTypeOfGlobal: failed to find " ++ show ident ++ " in module."
      Just d -> scSharedTerm sc (defType d)

scTypeOfDataType :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfDataType sc ident =
    case findDataType (scModule sc) ident of
      Nothing -> fail $ "scTypeOfDataType: failed to find " ++ show ident ++ " in module."
      Just d -> scSharedTerm sc (dtType d)

scTypeOfCtor :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfCtor sc ident =
    case findCtor (scModule sc) ident of
      Nothing -> fail $ "scTypeOfCtor: failed to find " ++ show ident ++ " in module."
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
    memo STApp{ stAppIndex = i, stAppTermF = t} = do
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
        UnitValue -> lift $ scUnitType sc
        UnitType -> lift $ scSort sc (mkSort 0)
        PairValue x y -> do
          tx <- memo x
          ty <- memo y
          lift $ scPairType sc tx ty
        PairType x y -> do
          sx <- sort x
          sy <- sort y
          lift $ scSort sc (max sx sy)
        PairLeft t -> do
          STApp{ stAppTermF = FTermF (PairType t1 _) } <- memo t >>= liftIO . scWhnf sc
          return t1
        PairRight t -> do
          STApp{ stAppTermF = FTermF (PairType _ t2) } <- memo t >>= liftIO . scWhnf sc
          return t2
        EmptyValue -> lift $ scEmptyType sc
        EmptyType -> lift $ scSort sc (mkSort 0)
        FieldValue f x y -> do
          tx <- memo x
          ty <- memo y
          lift $ scFieldType sc f tx ty
        FieldType _ x y -> do
          sx <- sort x
          sy <- sort y
          lift $ scSort sc (max sx sy)
        RecordSelector t f -> do
          f' <- asStringLit =<< liftIO (scWhnf sc f)
          t' <- memo t >>= liftIO . scWhnf sc
          m <- asRecordType t'
          let Just tp = Map.lookup f' m
          return tp
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
    STApp{ stAppTermF = FTermF (Sort s) } -> return s
    _ -> fail $ "Not a sort: " ++ show tp

alphaEquiv :: SharedTerm s -> SharedTerm s -> Bool
alphaEquiv = term
  where
    term (Unshared tf1) (Unshared tf2) = termf tf1 tf2
    term (Unshared tf1) (STApp{ stAppTermF = tf2}) = termf tf1 tf2
    term (STApp{ stAppTermF = tf1}) (Unshared tf2) = termf tf1 tf2
    term (STApp{ stAppIndex = i1, stAppTermF = tf1})
         (STApp{ stAppIndex = i2, stAppTermF = tf2}) = i1 == i2 || termf tf1 tf2
    termf (FTermF ftf1) (FTermF ftf2) = ftermf ftf1 ftf2
    termf (App t1 u1) (App t2 u2) = term t1 t2 && term u1 u2
    termf (Lambda _ t1 u1) (Lambda _ t2 u2) = term t1 t2 && term u1 u2
    termf (Pi _ t1 u1) (Pi _ t2 u2) = term t1 t2 && term u1 u2
    termf (LocalVar i1) (LocalVar i2) = i1 == i2
    termf (Constant _ _ tf1) (Constant _ _ tf2) = term tf1 tf2
    termf _ _ = False
    ftermf ftf1 ftf2 = case zipWithFlatTermF term ftf1 ftf2 of
                         Nothing -> False
                         Just ftf3 -> Fold.and ftf3

--------------------------------------------------------------------------------

-- | The inverse function to @scSharedTerm@.
unshare :: forall s. SharedTerm s -> Term
unshare t0 = State.evalState (go t0) Map.empty
  where
    go :: SharedTerm s -> State.State (Map TermIndex Term) Term
    go (Unshared t) = Term <$> traverse go t
    go (STApp{ stAppIndex = i, stAppTermF = t}) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          x <- Term <$> traverse go t
          State.modify (Map.insert i x)
          return x

instance Show (SharedTerm s) where
  show = scPrettyTerm

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
    go cache (Unshared tf) =
          Unshared <$> traverse (go cache) tf
    go cache (STApp{ stAppIndex = idx, stAppTermF = tf}) =
          useCache cache idx (scTermF sc =<< traverse (go cache) tf)

--------------------------------------------------------------------------------

-- | Returns bitset containing indices of all free local variables.
looseVars :: SharedTerm s -> BitSet
looseVars STApp{ stAppFreeVars = x } = x
looseVars (Unshared f) = freesTermF (fmap looseVars f)

-- | Compute the value of the smallest variable in the term, if any.
smallestFreeVar :: SharedTerm s -> Maybe Int
smallestFreeVar t
   | fv == 0 = Nothing
   | fv > 0  = Just $! go 0 fv
   | otherwise = error "impossible: negative free variable bitset!"

 where fv = looseVars t

       go :: Int -> Integer -> Int
       go !shft !x
          | xw == 0   = go (shft+64) (shiftR x 64)
          | otherwise = shft + countTrailingZeros xw

        where xw :: Word64
              xw = fromInteger x

--------------------------------------------------------------------------------
-- Instantiating variables

instantiateVars :: forall s. SharedContext s
                -> (DeBruijnIndex -> Either (ExtCns (SharedTerm s)) DeBruijnIndex -> IO (SharedTerm s))
                -> DeBruijnIndex -> SharedTerm s -> IO (SharedTerm s)
instantiateVars sc f initialLevel t0 =
    do cache <- newCache
       let ?cache = cache in go initialLevel t0
  where
    go :: (?cache :: Cache IORef (TermIndex, DeBruijnIndex) (SharedTerm s)) =>
          DeBruijnIndex -> SharedTerm s -> IO (SharedTerm s)
    go l (Unshared tf) =
            go' l tf
    go l (STApp{ stAppIndex = tidx, stAppTermF = tf}) =
            useCache ?cache (tidx, l) (go' l tf)

    go' :: (?cache :: Cache IORef (TermIndex, DeBruijnIndex) (SharedTerm s)) =>
           DeBruijnIndex -> TermF (SharedTerm s) -> IO (SharedTerm s)
    go' l (FTermF (ExtCns ec)) = f l (Left ec)
    go' l (FTermF tf)       = scFlatTermF sc =<< (traverse (go l) tf)
    go' l (App x y)         = scTermF sc =<< (App <$> go l x <*> go l y)
    go' l (Lambda i tp rhs) = scTermF sc =<< (Lambda i <$> go l tp <*> go (l+1) rhs)
    go' l (Pi i lhs rhs)    = scTermF sc =<< (Pi i <$> go l lhs <*> go (l+1) rhs)
    go' l (Let defs r) = scTermF sc =<< (Let <$> traverse procDef defs <*> go l' r)
      where l' = l + length defs
            procDef :: LocalDef (SharedTerm s) -> IO (LocalDef (SharedTerm s))
            procDef (Def sym qual tp eqs) = Def sym qual <$> go l tp <*> traverse procEq eqs
            procEq :: DefEqn (SharedTerm s) -> IO (DefEqn (SharedTerm s))
            procEq (DefEqn pats rhs) = DefEqn pats <$> go eql rhs
              where eql = l' + sum (patBoundVarCount <$> pats)
    go' l (LocalVar i)
      | i < l     = scTermF sc (LocalVar i)
      | otherwise = f l (Right i)
    go' _ tf@(Constant _ _ _) = scTermF sc tf

-- | @incVars j k t@ increments free variables at least @initialLevel@ by @j@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVars :: SharedContext s
        -> DeBruijnIndex -> DeBruijnIndex -> SharedTerm s -> IO (SharedTerm s)
incVars sc initialLevel j
  | j == 0    = return
  | otherwise = instantiateVars sc fn initialLevel
  where
    fn _ (Left ec) = scFlatTermF sc $ ExtCns ec
    fn _ (Right i) = scTermF sc (LocalVar (i+j))

-- | Substitute @t0@ for variable @k@ in @t@ and decrement all higher
-- dangling variables.
instantiateVar :: forall s. SharedContext s
               -> DeBruijnIndex -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
instantiateVar sc k t0 t =
    do cache <- newCache
       let ?cache = cache in instantiateVars sc fn 0 t
  where -- Use map reference to memoize instantiated versions of t.
        term :: (?cache :: Cache IORef DeBruijnIndex (SharedTerm s)) =>
                DeBruijnIndex -> IO (SharedTerm s)
        term i = useCache ?cache i (incVars sc 0 i t0)
        -- Instantiate variable 0.
        fn :: (?cache :: Cache IORef DeBruijnIndex (SharedTerm s)) =>
              DeBruijnIndex -> Either (ExtCns (SharedTerm s)) DeBruijnIndex -> IO (SharedTerm s)
        fn _ (Left ec) = scFlatTermF sc $ ExtCns ec
        fn i (Right j)
               | j  > i + k = scTermF sc (LocalVar (j - 1))
               | j == i + k = term i
               | otherwise  = scTermF sc (LocalVar j)

-- | Substitute @ts@ for variables @[k .. k + length ts - 1]@ and
-- decrement all higher loose variables by @length ts@.
instantiateVarList :: forall s. SharedContext s
                   -> DeBruijnIndex -> [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
instantiateVarList _ _ [] t = return t
instantiateVarList sc k ts t =
    do caches <- mapM (const newCache) ts
       instantiateVars sc (fn (zip caches ts)) 0 t
  where
    l = length ts
    -- Memoize instantiated versions of ts.
    term :: (Cache IORef DeBruijnIndex (SharedTerm s), SharedTerm s)
         -> DeBruijnIndex -> IO (SharedTerm s)
    term (cache, x) i = useCache cache i (incVars sc 0 i x)
    -- Instantiate variables [k .. k+l-1].
    fn :: [(Cache IORef DeBruijnIndex (SharedTerm s), SharedTerm s)]
       -> DeBruijnIndex -> Either (ExtCns (SharedTerm s)) DeBruijnIndex -> IO (SharedTerm s)
    fn _ _ (Left ec) = scFlatTermF sc $ ExtCns ec
    fn rs i (Right j)
              | j >= i + k + l = scTermF sc (LocalVar (j - l))
              | j >= i + k     = term (rs !! (j - i - k)) i
              | otherwise      = scTermF sc (LocalVar j)

--------------------------------------------------------------------------------
-- Beta Normalization

betaNormalize :: forall s. SharedContext s -> SharedTerm s -> IO (SharedTerm s)
betaNormalize sc t0 =
  do cache <- newCache
     let ?cache = cache in go t0
  where
    go :: (?cache :: Cache IORef TermIndex (SharedTerm s)) => SharedTerm s -> IO (SharedTerm s)
    go t = case t of
      Unshared _ -> go' t
      STApp{ stAppIndex = i } -> useCache ?cache i (go' t)

    go' :: (?cache :: Cache IORef TermIndex (SharedTerm s)) => SharedTerm s -> IO (SharedTerm s)
    go' t = do
      let (f, args) = asApplyAll t
      let (params, body) = asLambdaList f
      let n = length (zip args params)
      if n == 0 then go3 t else do
        body' <- go body
        f' <- scLambdaList sc (drop n params) body'
        args' <- mapM go args
        f'' <- instantiateVarList sc 0 (reverse (take n args')) f'
        scApplyAll sc f'' (drop n args')

    go3 :: (?cache :: Cache IORef TermIndex (SharedTerm s)) => SharedTerm s -> IO (SharedTerm s)
    go3 (Unshared tf) = Unshared <$> traverseTF go tf
    go3 (STApp{ stAppTermF = tf }) = scTermF sc =<< traverseTF go tf

    traverseTF :: (a -> IO a) -> TermF a -> IO (TermF a)
    traverseTF _ tf@(Constant _ _ _) = pure tf
    traverseTF f tf = traverse f tf

--------------------------------------------------------------------------------
-- Pretty printing

type OccurrenceMap s = IntMap (SharedTerm s, Word64)

-- | Returns map that associated each term index appearing in the term
-- to the number of occurrences in the shared term.
scTermCount :: SharedTerm s -> OccurrenceMap s
scTermCount t0 = execState (go [t0]) IntMap.empty
  where go :: [SharedTerm s] -> State (OccurrenceMap s) ()
        go [] = return ()
        go (t:r) =
          case t of
            Unshared _ -> recurse
            STApp{ stAppIndex = i } -> do
              m <- get
              case IntMap.lookup i m of
                Just (_, n) -> do
                  put $ n `seq` IntMap.insert i (t, n+1) m
                  go r
                Nothing -> do
                  when (looseVars t == 0) $ put (IntMap.insert i (t, 1) m)
                  recurse
          where
            recurse = do
              let (h,args) = asApplyAll t
              case unwrapTermF h of
                Constant{} -> go (args ++ r)
                tf -> go (Fold.foldr' (:) (args++r) tf)

lineSep :: [Doc] -> Doc
lineSep l = hcat (punctuate line l)

scPrettyTermDoc :: forall s . SharedTerm s -> Doc
scPrettyTermDoc t0
    | null bound = ppTermDoc (ppt lcls0 PrecNone t0)
    | otherwise =
        text "let { " <> nest 6 (lineSep lets) <$$>
        text "    }" <$$>
        text " in " <> align (ppTermDoc (ppt lcls0 PrecNone t0))
  where lcls0 = emptyLocalVarDoc
        cm = scTermCount t0 -- Occurrence map
        -- Return true if variable should be introduced to name term.
        shouldName :: SharedTerm s -> Word64 -> Bool
        shouldName t c =
          case unwrapTermF t of
            FTermF GlobalDef{} -> False
            FTermF UnitValue -> False
            FTermF UnitType -> False
            FTermF EmptyValue -> False
            FTermF EmptyType -> False
            FTermF (CtorApp _ []) -> False
            FTermF (DataTypeApp _ []) -> False
            FTermF NatLit{} -> False
            FTermF (ArrayValue _ v) | V.length v == 0 -> False
            FTermF FloatLit{} -> False
            FTermF DoubleLit{} -> False
            FTermF StringLit{} -> False
            FTermF ExtCns{} -> False
            LocalVar{} -> False
            _ -> c > 1

        -- Terms bound in map.
        bound :: [(TermIndex, SharedTerm s)]
        bound = [ (i, t) | (i, (t,c)) <- IntMap.assocs cm, shouldName t c ]

        var :: Word64 -> Doc
        var n = char 'x' <> integer (toInteger n)

        lets = [ var n <+> char '=' <+> ppTermDoc (ppTermF ppt lcls0 PrecNone (unwrapTermF t)) <> char ';'
               | ((_, t), n) <- bound `zip` [0..]
               ]

        dm :: IntMap Doc
        dm = Fold.foldl' insVar IntMap.empty (bound `zip` [0..])
          where insVar m ((i, _), n) = IntMap.insert i (var n) m

        ppt :: LocalVarDoc -> Prec -> SharedTerm s -> TermDoc
        ppt lcls p (Unshared tf) = ppTermF ppt lcls p tf
        ppt lcls p (STApp{ stAppIndex = i, stAppTermF = tf}) =
          case IntMap.lookup i dm of
            Just d -> TermDoc d
            Nothing -> ppTermF ppt lcls p tf

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
scRecord sc m = go (Map.assocs m)
  where go [] = scEmptyValue sc
        go ((f, x) : xs) = do l <- scString sc f
                              r <- go xs
                              scFieldValue sc l x r

scRecordSelect :: SharedContext s -> SharedTerm s -> FieldName -> IO (SharedTerm s)
scRecordSelect sc t fname = do
  l <- scString sc fname
  scFlatTermF sc (RecordSelector t l)

scRecordType :: SharedContext s -> Map FieldName (SharedTerm s) -> IO (SharedTerm s)
scRecordType sc m = go (Map.assocs m)
  where go [] = scEmptyType sc
        go ((f, x) : xs) = do l <- scString sc f
                              r <- go xs
                              scFieldType sc l x r

scUnitValue :: SharedContext s -> IO (SharedTerm s)
scUnitValue sc = scFlatTermF sc UnitValue

scUnitType :: SharedContext s -> IO (SharedTerm s)
scUnitType sc = scFlatTermF sc UnitType

scPairValue :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scPairValue sc x y = scFlatTermF sc (PairValue x y)

scPairType :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scPairType sc x y = scFlatTermF sc (PairType x y)

scEmptyValue :: SharedContext s -> IO (SharedTerm s)
scEmptyValue sc = scFlatTermF sc EmptyValue

scEmptyType :: SharedContext s -> IO (SharedTerm s)
scEmptyType sc = scFlatTermF sc EmptyType

scFieldValue :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scFieldValue sc f x y = scFlatTermF sc (FieldValue f x y)

scFieldType :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scFieldType sc f x y = scFlatTermF sc (FieldType f x y)

scTuple :: SharedContext s -> [SharedTerm s] -> IO (SharedTerm s)
scTuple sc [] = scUnitValue sc
scTuple sc (t : ts) = scPairValue sc t =<< scTuple sc ts

scTupleType :: SharedContext s -> [SharedTerm s] -> IO (SharedTerm s)
scTupleType sc [] = scUnitType sc
scTupleType sc (t : ts) = scPairType sc t =<< scTupleType sc ts

scPairLeft :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scPairLeft sc t = scFlatTermF sc (PairLeft t)

scPairRight :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scPairRight sc t = scFlatTermF sc (PairRight t)

scPairSelector :: SharedContext s -> SharedTerm s -> Bool -> IO (SharedTerm s)
scPairSelector sc t False = scPairLeft sc t
scPairSelector sc t True = scPairRight sc t

scTupleSelector :: SharedContext s -> SharedTerm s -> Int -> IO (SharedTerm s)
scTupleSelector sc t i
  | i == 1    = scPairLeft sc t
  | i > 1     = do t' <- scPairRight sc t
                   scTupleSelector sc t' (i - 1)
  | otherwise = fail "scTupleSelector: non-positive index"

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

scImplies :: SharedContext s -> SharedTerm s -> SharedTerm s
          -> IO (SharedTerm s)
scImplies sc x y = scGlobalApply sc "Prelude.implies" [x,y]

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

scMinNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s) 
scMinNat sc x y = scGlobalApply sc "Prelude.minNat" [x,y]

scMaxNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s) 
scMaxNat sc x y = scGlobalApply sc "Prelude.maxNat" [x,y]

-- Primitive operations on Integer

scInteger :: SharedContext s -> IO (SharedTerm s)
scInteger sc = scDataTypeApp sc "Prelude.Integer" []

-- primitive intAdd/intSub/intMul/intDiv/intMod :: Integer -> Integer -> Integer;
scIntAdd, scIntSub, scIntMul, scIntDiv, scIntMod, scIntMax, scIntMin
   :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scIntAdd sc x y = scGlobalApply sc "Prelude.intAdd" [x, y]
scIntSub sc x y = scGlobalApply sc "Prelude.intSub" [x, y]
scIntMul sc x y = scGlobalApply sc "Prelude.intMul" [x, y]
scIntDiv sc x y = scGlobalApply sc "Prelude.intDiv" [x, y]
scIntMod sc x y = scGlobalApply sc "Prelude.intMod" [x, y]
scIntMin sc x y = scGlobalApply sc "Prelude.intMin" [x, y]
scIntMax sc x y = scGlobalApply sc "Prelude.intMax" [x, y]

-- primitive intNeg :: Integer -> Integer;
scIntNeg
   :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scIntNeg sc x = scGlobalApply sc "Prelude.intNeg" [x]

-- primitive intEq/intLe/intLt  :: Integer -> Integer -> Bool;
scIntEq, scIntLe, scIntLt
   :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scIntEq sc x y = scGlobalApply sc "Prelude.intEq" [x, y]
scIntLe sc x y = scGlobalApply sc "Prelude.intLe" [x, y]
scIntLt sc x y = scGlobalApply sc "Prelude.intLt" [x, y]

-- primitive intToNat :: Integer -> Nat;
scIntToNat
   :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scIntToNat sc x = scGlobalApply sc "Prelude.intToNat" [x]

-- primitive natToInt :: Nat -> Integer;
scNatToInt
   :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scNatToInt sc x = scGlobalApply sc "Prelude.natToInt" [x]

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
scIntToBv
   :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scIntToBv sc n x = scGlobalApply sc "Prelude.intToBv" [n,x]

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
scBvToInt
   :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvToInt sc n x = scGlobalApply sc "Prelude.bvToInt" [n,x]

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
scSbvToInt
   :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scSbvToInt sc n x = scGlobalApply sc "Prelude.sbvToInt" [n,x]


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

-- | bvBool :: (n :: Nat) -> Bool -> bitvector n;
scBvBool :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvBool sc n x = scGlobalApply sc "Prelude.bvBool" [n, x]

-- | bvNonzero :: (n :: Nat) -> bitvector n -> Bool;
scBvNonzero :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvNonzero sc n x = scGlobalApply sc "Prelude.bvNonzero" [n, x]

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

-- | updNatFun :: (a::sort 0) -> (Nat -> a) -> Nat -> a -> (Nat -> a);
scUpdNatFun :: SharedContext s -> SharedTerm s -> SharedTerm s
            -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scUpdNatFun sc a f i v = scGlobalApply sc "Prelude.updNatFun" [a, f, i, v]

-- | updBvFun :: (n::Nat) -> (a::sort 0) -> (bitvector n -> a) -> bitvector n -> a -> (bitvector n -> a);
scUpdBvFun :: SharedContext s -> SharedTerm s -> SharedTerm s
           -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scUpdBvFun sc n a f i v = scGlobalApply sc "Prelude.updBvFun" [n, a, f, i, v]

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

-- | Return a list of all ExtCns subterms in the given term, sorted by
-- index. Does not traverse the unfoldings of @Constant@ terms.
getAllExts :: SharedTerm s -> [ExtCns (SharedTerm s)]
getAllExts t = Set.toList (getAllExtSet t)

-- | Return a set of all ExtCns subterms in the given term.
--   Does not traverse the unfoldings of @Constant@ terms.
getAllExtSet :: SharedTerm s -> Set.Set (ExtCns (SharedTerm s))
getAllExtSet t = snd $ getExtCns (Set.empty, Set.empty) t
    where getExtCns acc@(is, _) (STApp{ stAppIndex = idx }) | Set.member idx is = acc
          getExtCns (is, a) (STApp{ stAppIndex = idx, stAppTermF = (FTermF (ExtCns ec)) }) =
            (Set.insert idx is, Set.insert ec a)
          getExtCns (is, a) (Unshared (FTermF (ExtCns ec))) =
            (is, Set.insert ec a)
          getExtCns acc (STApp{ stAppTermF = Constant _ _ _ }) = acc
          getExtCns acc (Unshared (Constant _ _ _)) = acc
          getExtCns (is, a) (STApp{ stAppIndex = idx, stAppTermF = tf'}) =
            foldl' getExtCns (Set.insert idx is, a) tf'
          getExtCns acc (Unshared tf') =
            foldl' getExtCns acc tf'

getConstantSet :: SharedTerm s -> Map String (SharedTerm s, SharedTerm s)
getConstantSet t = snd $ go (Set.empty, Map.empty) t
  where
    go acc@(idxs, names) (STApp{ stAppIndex = i, stAppTermF = tf})
      | Set.member i idxs = acc
      | otherwise         = termf (Set.insert i idxs, names) tf
    go acc (Unshared tf) = termf acc tf

    termf acc@(idxs, names) tf =
      case tf of
        Constant n ty body -> (idxs, Map.insert n (ty, body) names)
        _ -> foldl' go acc tf

-- | Instantiate some of the external constants
scInstantiateExt :: forall s
                  . SharedContext s
                 -> Map VarIndex (SharedTerm s)
                 -> SharedTerm s
                 -> IO (SharedTerm s)
scInstantiateExt sc vmap = instantiateVars sc fn 0
  where fn l (Left ec) =
            case Map.lookup (ecVarIndex ec) vmap of
               Just t  -> incVars sc 0 l t
               Nothing -> scFlatTermF sc $ ExtCns ec
        fn _ (Right i) = scTermF sc $ LocalVar i

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


scUnfoldConstants :: forall s. SharedContext s -> [String] -> SharedTerm s -> IO (SharedTerm s)
scUnfoldConstants sc names t0 = scUnfoldConstantSet sc True (Set.fromList names) t0

-- | TODO: test whether this version is slower or faster.
scUnfoldConstants' :: forall s. SharedContext s -> [String] -> SharedTerm s -> IO (SharedTerm s)
scUnfoldConstants' sc names t0 = scUnfoldConstantSet' sc True (Set.fromList names) t0

scUnfoldConstantSet :: forall s. SharedContext s
                    -> Bool  -- ^ True: unfold constants in set. False: unfold constants NOT in set
                    -> Set String -- ^ Set of constant names
                    -> SharedTerm s
                    -> IO (SharedTerm s)
scUnfoldConstantSet sc b names t0 = do
  cache <- newCache
  let go :: SharedTerm s -> IO (SharedTerm s)
      go t@(Unshared tf) =
        case tf of
          Constant name rhs _
            | Set.member name names == b -> go rhs
            | otherwise                  -> return t
          _ -> Unshared <$> traverse go tf
      go t@(STApp{ stAppIndex = idx, stAppTermF = tf }) = useCache cache idx $
        case tf of
          Constant name rhs _
            | Set.member name names == b -> go rhs
            | otherwise         -> return t
          _ -> scTermF sc =<< traverse go tf
  go t0


-- | TODO: test whether this version is slower or faster.
scUnfoldConstantSet' :: forall s. SharedContext s
                    -> Bool  -- ^ True: unfold constants in set. False: unfold constants NOT in set
                    -> Set String -- ^ Set of constant names
                    -> SharedTerm s
                    -> IO (SharedTerm s)
scUnfoldConstantSet' sc b names t0 = do
  tcache <- newCacheMap' Map.empty
  let go :: SharedTerm s -> ChangeT IO (SharedTerm s)
      go t@(Unshared tf) =
        case tf of
          Constant name rhs _
            | Set.member name names == b -> taint (go rhs)
            | otherwise                  -> pure t
          _ -> whenModified t (return . Unshared) (traverse go tf)
      go t@(STApp{ stAppIndex = idx, stAppTermF = tf }) =
        case tf of
          Constant name rhs _
            | Set.member name names == b -> taint (go rhs)
            | otherwise                  -> pure t
          _ -> useChangeCache tcache idx $
                 whenModified t (scTermF sc) (traverse go tf)
  commitChangeT (go t0)


-- | Return the number of DAG nodes used by the given @SharedTerm@.
scSharedSize :: SharedTerm s -> Integer
scSharedSize = fst . go (0, Set.empty)
  where
    go (sz, seen) (Unshared tf) = foldl' go (strictPair (sz + 1) seen) tf
    go (sz, seen) (STApp{ stAppIndex = idx, stAppTermF = tf })
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
    go (sz, seen) (STApp{ stAppIndex = idx, stAppTermF = tf }) =
      case Map.lookup idx seen of
        Just sz' -> (sz + sz', seen)
        Nothing -> (sz + sz', Map.insert idx sz' seen')
          where (sz', seen') = foldl' go (1, seen) tf


-- | `openTerm sc nm ty i body` replaces the loose deBruijn variable `i`
--   with a fresh external constant (with name `nm`, and type `ty`) in `body`.
scOpenTerm :: SharedContext s
         -> String
         -> SharedTerm s
         -> DeBruijnIndex
         -> SharedTerm s
         -> IO (ExtCns (SharedTerm s), SharedTerm s)
scOpenTerm sc nm tp idx body = do
    v <- scFreshGlobalVar sc
    let ec = EC v nm tp
    ec_term <- scFlatTermF sc (ExtCns ec)
    body' <- instantiateVar sc idx ec_term body
    return (ec, body')

-- | `closeTerm closer sc ec body` replaces the external constant `ec` in `body` by
--   a new deBruijn variable and binds it using the binding form given by 'close'.
--   The name and type of the new bound variable are given by the name and type of `ec`.
scCloseTerm :: (SharedContext s -> String -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s))
          -> SharedContext s
          -> ExtCns (SharedTerm s)
          -> SharedTerm s
          -> IO (SharedTerm s)
scCloseTerm close sc ec body = do
    lv <- scLocalVar sc 0
    body' <- scInstantiateExt sc (Map.insert (ecVarIndex ec) lv Map.empty) =<< incVars sc 0 1 body
    close sc (ecName ec) (ecType ec) body'
