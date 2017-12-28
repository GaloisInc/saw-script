{-# LANGUAGE CPP #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ParallelListComp #-}

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
  , Term(..)
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
  , PPOpts(..)
  , defaultPPOpts
  , scPrettyTerm
  , scPrettyTermDoc
  , scGlobalApply
  , scSharedTerm
  , scImport
    -- ** Normalization
  , scWhnf
  , scConvertible
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
  , scIntegerType
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
  , scLsb, scMsb
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
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.IORef (IORef)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import Data.Word
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.Recognizer
import Verifier.SAW.Term.Functor
--import Verifier.SAW.Term.Pretty
import Verifier.SAW.TypedAST
import Verifier.SAW.Unique

#if !MIN_VERSION_base(4,8,0)
countTrailingZeros :: (FiniteBits b) => b -> Int
countTrailingZeros x = go 0
  where
    go i | i >= w      = i
         | testBit x i = i
         | otherwise   = go (i+1)
    w = finiteBitSize x
#endif

newtype Uninterp = Uninterp { getUninterp :: (String, Term) } deriving Show

------------------------------------------------------------
-- TermFMaps

-- | A TermFMap is a data structure used for hash-consing of terms.
data TermFMap a
  = TermFMap
  { appMapTFM :: !(IntMap (IntMap a))
  , hashMapTFM :: !(HashMap (TermF Term) a)
  }

emptyTFM :: TermFMap a
emptyTFM = TermFMap IntMap.empty HMap.empty

lookupTFM :: TermF Term -> TermFMap a -> Maybe a
lookupTFM tf tfm =
  case tf of
    App (STApp{ stAppIndex = i }) (STApp{ stAppIndex = j}) ->
      IntMap.lookup i (appMapTFM tfm) >>= IntMap.lookup j
    _ -> HMap.lookup tf (hashMapTFM tfm)

insertTFM :: TermF Term -> a -> TermFMap a -> TermFMap a
insertTFM tf x tfm =
  case tf of
    App (STApp{ stAppIndex = i }) (STApp{ stAppIndex = j}) ->
      let f Nothing = Just (IntMap.singleton j x)
          f (Just m) = Just (IntMap.insert j x m)
      in tfm { appMapTFM = IntMap.alter f i (appMapTFM tfm) }
    _ -> tfm { hashMapTFM = HMap.insert tf x (hashMapTFM tfm) }

----------------------------------------------------------------------
-- SharedContext: a high-level interface for building Terms.

data SharedContext = SharedContext
  { -- | Returns the current module for the underlying global theory.
    scModule        :: Module
  , scTermF         :: TermF Term -> IO Term
  , scFreshGlobalVar :: IO VarIndex
  }

scFlatTermF :: SharedContext -> FlatTermF Term -> IO Term
scFlatTermF sc ftf = scTermF sc (FTermF ftf)

-- | Create a global variable with the given identifier (which may be "_") and type.
scFreshGlobal :: SharedContext -> String -> Term -> IO Term
scFreshGlobal sc sym tp = do
  i <- scFreshGlobalVar sc
  scFlatTermF sc (ExtCns (EC i sym tp))

-- | Returns shared term associated with ident.
-- Does not check module namespace.
scGlobalDef :: SharedContext -> Ident -> IO Term
scGlobalDef sc ident = scFlatTermF sc (GlobalDef ident)

scApply :: SharedContext -> Term -> Term -> IO Term
scApply sc f = scTermF sc . App f

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scDataTypeApp :: SharedContext -> Ident -> [Term] -> IO Term
scDataTypeApp sc ident args = scFlatTermF sc (DataTypeApp ident args)

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scCtorApp :: SharedContext -> Ident -> [Term] -> IO Term
scCtorApp sc ident args = scFlatTermF sc (CtorApp ident args)

-- SharedContext implementation.

type AppCache = TermFMap Term

type AppCacheRef = MVar AppCache

emptyAppCache :: AppCache
emptyAppCache = emptyTFM

-- | Return term for application using existing term in cache if it is available.
getTerm :: AppCacheRef -> TermF Term -> IO Term
getTerm r a =
  modifyMVar r $ \s -> do
    case lookupTFM a s of
      Just t -> return (s, t)
      Nothing -> do
        i <- getUniqueInt
        let t = STApp { stAppIndex = i
                      , stAppFreeVars = freesTermF (fmap looseVars a)
                      , stAppTermF = a
                      }
        let s' = insertTFM a t s
        seq s' $ return (s', t)

--------------------------------------------------------------------------------
-- Reduction to head-normal form

-- | Reduces beta-redexes, tuple/record selectors, and definition
-- equations at the top level of a term, and evaluates all arguments
-- to type constructors (including function, record, and tuple types).
scWhnf :: SharedContext -> Term -> IO Term
scWhnf sc t0 =
  do cache <- newCacheIntMap
     let ?cache = cache in memo t0
  where
    memo :: (?cache :: Cache IORef TermIndex Term) => Term -> IO Term
    memo t =
      case t of
        Unshared _ -> go [] t
        STApp { stAppIndex = i } -> useCache ?cache i (go [] t)

    go :: (?cache :: Cache IORef TermIndex Term) =>
          [Either Term (Either Bool FieldName)] -> Term -> IO Term
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
    go xs                     (asConstant -> Just (_,body,_))   = do go xs body
    go xs                     t                                 = foldM reapply t xs

    reapply :: Term -> Either Term (Either Bool FieldName) -> IO Term
    reapply t (Left x) = scApply sc t x
    reapply t (Right (Left i)) = scPairSelector sc t i
    reapply t (Right (Right i)) = scRecordSelect sc t i

    tryEqns :: (?cache :: Cache IORef TermIndex Term) =>
               Ident -> [Either Term (Either Bool FieldName)] -> [DefEqn] -> IO Term
    tryEqns ident xs [] = scGlobalDef sc ident >>= flip (foldM reapply) xs
    tryEqns ident xs (DefEqn ps rhs : eqns) = do
      minst <- matchAll ps xs
      case minst of
        Just inst | and (zipWith (==) (Map.keys inst) [0..]) -> do
          rhs' <- scSharedTerm sc rhs
          t <- instantiateVarList sc 0 (reverse (Map.elems inst)) rhs'
          go (drop (length ps) xs) t
        _ -> tryEqns ident xs eqns

    matchAll :: (?cache :: Cache IORef TermIndex Term) =>
                [Pat] -> [Either Term (Either Bool FieldName)]
                  -> IO (Maybe (Map Int Term))
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

    match :: (?cache :: Cache IORef TermIndex Term) =>
             Pat -> Term -> IO (Maybe (Map Int Term))
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


-- | Test if two terms are convertible; that is, if they are equivalent under evaluation.
scConvertible :: SharedContext
              -> Bool -- ^ Should abstract constants be unfolded during this check?
              -> Term
              -> Term
              -> IO Bool
scConvertible sc unfoldConst tm1 tm2 = do
   c <- newCache
   go c tm1 tm2

 where whnf :: Cache IORef TermIndex Term -> Term -> IO (TermF Term)
       whnf _c t@(Unshared _) = unwrapTermF <$> scWhnf sc t
       whnf c t@(STApp{ stAppIndex = idx}) = unwrapTermF <$> (useCache c idx $ scWhnf sc t)

       go :: Cache IORef TermIndex Term -> Term -> Term -> IO Bool
       go _c (STApp{ stAppIndex = idx1}) (STApp{ stAppIndex = idx2})
           | idx1 == idx2 = return True   -- succeed early case
       go c t1 t2 = join (goF c <$> whnf c t1 <*> whnf c t2)

       goF :: Cache IORef TermIndex Term -> TermF Term -> TermF Term -> IO Bool

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

       -- final catch-all case
       goF _c x y = return $ alphaEquiv (Unshared x) (Unshared y)

--------------------------------------------------------------------------------
-- Type checking

reducePi :: SharedContext -> Term -> Term -> IO Term
reducePi sc t arg = do
  t' <- scWhnf sc t
  case asPi t' of
    Just (_, _, body) -> instantiateVar sc 0 arg body
    _                 -> fail $ unlines ["reducePi: not a Pi term", scPrettyTerm defaultPPOpts t']

scTypeOfGlobal :: SharedContext -> Ident -> IO Term
scTypeOfGlobal sc ident =
    case findDef (scModule sc) ident of
      Nothing -> fail $ "scTypeOfGlobal: failed to find " ++ show ident ++ " in module."
      Just d -> scSharedTerm sc (defType d)

scTypeOfDataType :: SharedContext -> Ident -> IO Term
scTypeOfDataType sc ident =
    case findDataType (scModule sc) ident of
      Nothing -> fail $ "scTypeOfDataType: failed to find " ++ show ident ++ " in module."
      Just d -> scSharedTerm sc (dtType d)

scTypeOfCtor :: SharedContext -> Ident -> IO Term
scTypeOfCtor sc ident =
    case findCtor (scModule sc) ident of
      Nothing -> fail $ "scTypeOfCtor: failed to find " ++ show ident ++ " in module."
      Just d -> scSharedTerm sc (ctorType d)

-- | Computes the type of a term as quickly as possible, assuming that
-- the term is well-typed.
scTypeOf :: SharedContext -> Term -> IO Term
scTypeOf sc t0 = scTypeOf' sc [] t0

-- | A version for open terms; the list argument encodes the type environment.
scTypeOf' :: SharedContext -> [Term] -> Term -> IO Term
scTypeOf' sc env t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: Term -> State.StateT (Map TermIndex Term) IO Term
    memo (Unshared t) = termf t
    memo STApp{ stAppIndex = i, stAppTermF = t} = do
      table <- State.get
      case Map.lookup i table of
        Just x  -> return x
        Nothing -> do
          x <- termf t
          State.modify (Map.insert i x)
          return x
    sort :: Term -> State.StateT (Map TermIndex Term) IO Sort
    sort t = asSort =<< memo t
    termf :: TermF Term -> State.StateT (Map TermIndex Term) IO Term
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
        LocalVar i
          | i < length env -> lift $ incVars sc 0 (i + 1) (env !! i)
          | otherwise      -> fail $ "Dangling bound variable: " ++ show (i - length env)
        Constant _ t _ -> memo t
    ftermf :: FlatTermF Term
           -> State.StateT (Map TermIndex Term) IO Term
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
          vec_f <- scFlatTermF sc preludeVecTypeFun
          scApplyAll sc vec_f [n, tp]
        FloatLit{}  -> lift $ scFlatTermF sc preludeFloatType
        DoubleLit{} -> lift $ scFlatTermF sc preludeDoubleType
        StringLit{} -> lift $ scFlatTermF sc preludeStringType
        ExtCns ec   -> return $ ecType ec

--------------------------------------------------------------------------------

-- | The inverse function to @scSharedTerm@.
unshare :: Term -> Term
unshare t0 = State.evalState (go t0) Map.empty
  where
    go :: Term -> State.State (Map TermIndex Term) Term
    go (Unshared t) = Unshared <$> traverse go t
    go (STApp{ stAppIndex = i, stAppTermF = t}) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          x <- Unshared <$> traverse go t
          State.modify (Map.insert i x)
          return x

-- | Perform hash-consing at every AST node to obtain maximal sharing.
scSharedTerm :: SharedContext -> Term -> IO Term
scSharedTerm sc = go
    where go t = scTermF sc =<< traverse go (unwrapTermF t)

-- | Imports a term built in a different shared context into the given
-- shared context. The caller must ensure that all the global constants
-- appearing in the term are valid in the new context.
scImport :: SharedContext -> Term -> IO Term
scImport sc t0 =
    do cache <- newCache
       go cache t0
  where
    go :: Cache IORef TermIndex Term -> Term -> IO Term
    go cache (Unshared tf) =
          Unshared <$> traverse (go cache) tf
    go cache (STApp{ stAppIndex = idx, stAppTermF = tf}) =
          useCache cache idx (scTermF sc =<< traverse (go cache) tf)

--------------------------------------------------------------------------------

-- | Returns bitset containing indices of all free local variables.
looseVars :: Term -> BitSet
looseVars STApp{ stAppFreeVars = x } = x
looseVars (Unshared f) = freesTermF (fmap looseVars f)

-- | Compute the value of the smallest variable in the term, if any.
smallestFreeVar :: Term -> Maybe Int
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

instantiateVars :: SharedContext
                -> (DeBruijnIndex -> Either (ExtCns Term) DeBruijnIndex -> IO Term)
                -> DeBruijnIndex -> Term -> IO Term
instantiateVars sc f initialLevel t0 =
    do cache <- newCache
       let ?cache = cache in go initialLevel t0
  where
    go :: (?cache :: Cache IORef (TermIndex, DeBruijnIndex) Term) =>
          DeBruijnIndex -> Term -> IO Term
    go l (Unshared tf) =
            go' l tf
    go l (STApp{ stAppIndex = tidx, stAppTermF = tf}) =
            useCache ?cache (tidx, l) (go' l tf)

    go' :: (?cache :: Cache IORef (TermIndex, DeBruijnIndex) Term) =>
           DeBruijnIndex -> TermF Term -> IO Term
    go' l (FTermF (ExtCns ec)) = f l (Left ec)
    go' l (FTermF tf)       = scFlatTermF sc =<< (traverse (go l) tf)
    go' l (App x y)         = scTermF sc =<< (App <$> go l x <*> go l y)
    go' l (Lambda i tp rhs) = scTermF sc =<< (Lambda i <$> go l tp <*> go (l+1) rhs)
    go' l (Pi i lhs rhs)    = scTermF sc =<< (Pi i <$> go l lhs <*> go (l+1) rhs)
    go' l (LocalVar i)
      | i < l     = scTermF sc (LocalVar i)
      | otherwise = f l (Right i)
    go' _ tf@(Constant _ _ _) = scTermF sc tf

-- | @incVars j k t@ increments free variables at least @initialLevel@ by @j@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVars :: SharedContext
        -> DeBruijnIndex -> DeBruijnIndex -> Term -> IO Term
incVars sc initialLevel j
  | j == 0    = return
  | otherwise = instantiateVars sc fn initialLevel
  where
    fn _ (Left ec) = scFlatTermF sc $ ExtCns ec
    fn _ (Right i) = scTermF sc (LocalVar (i+j))

-- | Substitute @t0@ for variable @k@ in @t@ and decrement all higher
-- dangling variables.
instantiateVar :: SharedContext
               -> DeBruijnIndex -> Term -> Term -> IO Term
instantiateVar sc k t0 t =
    do cache <- newCache
       let ?cache = cache in instantiateVars sc fn 0 t
  where -- Use map reference to memoize instantiated versions of t.
        term :: (?cache :: Cache IORef DeBruijnIndex Term) =>
                DeBruijnIndex -> IO Term
        term i = useCache ?cache i (incVars sc 0 i t0)
        -- Instantiate variable 0.
        fn :: (?cache :: Cache IORef DeBruijnIndex Term) =>
              DeBruijnIndex -> Either (ExtCns Term) DeBruijnIndex -> IO Term
        fn _ (Left ec) = scFlatTermF sc $ ExtCns ec
        fn i (Right j)
               | j  > i + k = scTermF sc (LocalVar (j - 1))
               | j == i + k = term i
               | otherwise  = scTermF sc (LocalVar j)

-- | Substitute @ts@ for variables @[k .. k + length ts - 1]@ and
-- decrement all higher loose variables by @length ts@.
instantiateVarList :: SharedContext
                   -> DeBruijnIndex -> [Term] -> Term -> IO Term
instantiateVarList _ _ [] t = return t
instantiateVarList sc k ts t =
    do caches <- mapM (const newCache) ts
       instantiateVars sc (fn (zip caches ts)) 0 t
  where
    l = length ts
    -- Memoize instantiated versions of ts.
    term :: (Cache IORef DeBruijnIndex Term, Term)
         -> DeBruijnIndex -> IO Term
    term (cache, x) i = useCache cache i (incVars sc 0 i x)
    -- Instantiate variables [k .. k+l-1].
    fn :: [(Cache IORef DeBruijnIndex Term, Term)]
       -> DeBruijnIndex -> Either (ExtCns Term) DeBruijnIndex -> IO Term
    fn _ _ (Left ec) = scFlatTermF sc $ ExtCns ec
    fn rs i (Right j)
              | j >= i + k + l = scTermF sc (LocalVar (j - l))
              | j >= i + k     = term (rs !! (j - i - k)) i
              | otherwise      = scTermF sc (LocalVar j)
-- ^ Specification in terms of @instantiateVar@ (by example):
-- @instantiateVarList 0 [x,y,z] t@ is the beta-reduced form of @Lam
-- (Lam (Lam t)) `App` z `App` y `App` x@, i.e. @instantiateVarList 0
-- [x,y,z] t == instantiateVar 0 x (instantiateVar 1 (incVars 0 1 y)
-- (instantiateVar 2 (incVars 0 2 z) t))@.

--------------------------------------------------------------------------------
-- Beta Normalization

betaNormalize :: SharedContext -> Term -> IO Term
betaNormalize sc t0 =
  do cache <- newCache
     let ?cache = cache in go t0
  where
    go :: (?cache :: Cache IORef TermIndex Term) => Term -> IO Term
    go t = case t of
      Unshared _ -> go' t
      STApp{ stAppIndex = i } -> useCache ?cache i (go' t)

    go' :: (?cache :: Cache IORef TermIndex Term) => Term -> IO Term
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

    go3 :: (?cache :: Cache IORef TermIndex Term) => Term -> IO Term
    go3 (Unshared tf) = Unshared <$> traverseTF go tf
    go3 (STApp{ stAppTermF = tf }) = scTermF sc =<< traverseTF go tf

    traverseTF :: (a -> IO a) -> TermF a -> IO (TermF a)
    traverseTF _ tf@(Constant _ _ _) = pure tf
    traverseTF f tf = traverse f tf

--------------------------------------------------------------------------------
-- Pretty printing

type OccurrenceMap s = IntMap (Term, Int)

-- | Returns map that associates each term index appearing in the term
-- to the number of occurrences in the shared term. Subterms that are
-- on the left-hand side of an application are excluded. The boolean
-- flag indicates whether to descend under lambdas and other binders.
scTermCount :: Bool -> Term -> OccurrenceMap s
scTermCount doBinders t0 = execState (go [t0]) IntMap.empty
  where go :: [Term] -> State (OccurrenceMap s) ()
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
                  put (IntMap.insert i (t, 1) m)
                  recurse
          where
            recurse = do
              let (h,args) = asApplyAll t
              go (Fold.foldr' (:) (args ++ r) (subterms h))
        subterms h =
          case unwrapTermF h of
            Lambda _ t1 _ | not doBinders -> [t1]
            Pi _ t1 _     | not doBinders -> [t1]
            Constant{}                    -> []
            tf                            -> Fold.toList tf

scPrettyTermDoc :: PPOpts -> Term -> Doc
scPrettyTermDoc opts t0 =
  ppLets lets0 (ppTermDoc (ppt (n0, dm0) False lcls0 PrecNone t0))
  where
    lcls0 = emptyLocalVarDoc

    -- | Terms in top-level let block.
    cm0 :: IntMap Term
    cm0 =
      IntMap.filter (\t -> looseVars t == 0) $ fmap fst $
      IntMap.filter shouldName (scTermCount True t0) -- Occurrence map

    -- Terms bound in map.
    bound0 :: [(TermIndex, Term)]
    bound0 = IntMap.assocs cm0

    lets0 = [ ppEqn m (n0, dm0) lcls0 PrecNone t | ((_, t), m) <- bound0 `zip` [0..] ]

    dm0 :: IntMap Doc
    dm0 = IntMap.fromList (zip (IntMap.keys cm0) (map var [0..]))

    n0 :: Int
    n0 = IntMap.size dm0

    ppLets :: [Doc] -> Doc -> Doc
    ppLets lets doc
      | null lets = doc
      | otherwise = ppLetBlock lets doc

    -- | Return true if variable should be introduced to name term.
    shouldName :: (Term, Int) -> Bool
    shouldName (t, c) =
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

    var :: Int -> Doc
    var n = char 'x' <> integer (toInteger n)

    ppEqn :: Int -> (Int, IntMap Doc) -> LocalVarDoc -> Prec -> Term -> Doc
    ppEqn m (n, dm) lcls p t =
      var m <+> char '=' <+>
      ppTermDoc (ppTermF opts (ppt (n, dm)) lcls p (unwrapTermF t)) <> char ';'

    ppt :: (Int, IntMap Doc) -> Bool -> LocalVarDoc -> Prec -> Term -> TermDoc
    ppt (n, dm) False lcls p (Unshared tf) = ppTermF opts (ppt (n, dm)) lcls p tf
    ppt (n, dm) False lcls p (STApp{stAppIndex = i, stAppTermF = tf}) =
      case IntMap.lookup i dm of
        Just d -> TermDoc d
        Nothing -> ppTermF opts (ppt (n, dm)) lcls p tf
    ppt (n, dm) True lcls _p t =
      TermDoc $ ppLets lets (ppTermDoc (ppt (n', dm') False lcls PrecNone t))
      where
        cm1 = fmap fst $ IntMap.filter shouldName (scTermCount False t)
        cm = IntMap.difference cm1 dm0 -- remove already-named entries
        dm1 = IntMap.fromList (zip (IntMap.keys cm) (map var [n ..]))
        dm' = IntMap.union dm dm1
        n' = n + IntMap.size cm
        lets = [ ppEqn m (n', dm') lcls PrecNone rhs
               | (rhs, m) <- IntMap.elems cm `zip` [n ..] ]

scPrettyTerm :: PPOpts -> Term -> String
scPrettyTerm opts t = show (scPrettyTermDoc opts t)

--------------------------------------------------------------------------------
-- Building shared terms

scApplyAll :: SharedContext -> Term -> [Term] -> IO Term
scApplyAll sc = foldlM (scApply sc)

-- | Returns the defined constant with the given name. Fails if no
-- such constant exists in the module.
scLookupDef :: SharedContext -> Ident -> IO Term
scLookupDef sc ident = scGlobalDef sc ident --FIXME: implement module check.

-- | Deprecated. Use scGlobalDef or scLookupDef instead.
scDefTerm :: SharedContext -> Def -> IO Term
scDefTerm sc d = scGlobalDef sc (defIdent d)

-- TODO: implement version of scCtorApp that looks up the arity of the
-- constructor identifier in the module.

-- | Deprecated. Use scCtorApp instead.
scApplyCtor :: SharedContext -> TypedCtor -> [Term] -> IO Term
scApplyCtor sc c args = scCtorApp sc (ctorName c) args

scSort :: SharedContext -> Sort -> IO Term
scSort sc s = scFlatTermF sc (Sort s)

scNat :: SharedContext -> Nat -> IO Term
scNat sc n = scFlatTermF sc (NatLit (toInteger n))

scString :: SharedContext -> String -> IO Term
scString sc s = scFlatTermF sc (StringLit s)

scVector :: SharedContext -> Term -> [Term] -> IO Term
scVector sc e xs = scFlatTermF sc (ArrayValue e (V.fromList xs))

scRecord :: SharedContext -> Map FieldName Term -> IO Term
scRecord sc m = go (Map.assocs m)
  where go [] = scEmptyValue sc
        go ((f, x) : xs) = do l <- scString sc f
                              r <- go xs
                              scFieldValue sc l x r

scRecordSelect :: SharedContext -> Term -> FieldName -> IO Term
scRecordSelect sc t fname = do
  l <- scString sc fname
  scFlatTermF sc (RecordSelector t l)

scRecordType :: SharedContext -> Map FieldName Term -> IO Term
scRecordType sc m = go (Map.assocs m)
  where go [] = scEmptyType sc
        go ((f, x) : xs) = do l <- scString sc f
                              r <- go xs
                              scFieldType sc l x r

scUnitValue :: SharedContext -> IO Term
scUnitValue sc = scFlatTermF sc UnitValue

scUnitType :: SharedContext -> IO Term
scUnitType sc = scFlatTermF sc UnitType

scPairValue :: SharedContext -> Term -> Term -> IO Term
scPairValue sc x y = scFlatTermF sc (PairValue x y)

scPairType :: SharedContext -> Term -> Term -> IO Term
scPairType sc x y = scFlatTermF sc (PairType x y)

scEmptyValue :: SharedContext -> IO Term
scEmptyValue sc = scFlatTermF sc EmptyValue

scEmptyType :: SharedContext -> IO Term
scEmptyType sc = scFlatTermF sc EmptyType

scFieldValue :: SharedContext -> Term -> Term -> Term -> IO Term
scFieldValue sc f x y = scFlatTermF sc (FieldValue f x y)

scFieldType :: SharedContext -> Term -> Term -> Term -> IO Term
scFieldType sc f x y = scFlatTermF sc (FieldType f x y)

scTuple :: SharedContext -> [Term] -> IO Term
scTuple sc [] = scUnitValue sc
scTuple sc (t : ts) = scPairValue sc t =<< scTuple sc ts

scTupleType :: SharedContext -> [Term] -> IO Term
scTupleType sc [] = scUnitType sc
scTupleType sc (t : ts) = scPairType sc t =<< scTupleType sc ts

scPairLeft :: SharedContext -> Term -> IO Term
scPairLeft sc t = scFlatTermF sc (PairLeft t)

scPairRight :: SharedContext -> Term -> IO Term
scPairRight sc t = scFlatTermF sc (PairRight t)

scPairSelector :: SharedContext -> Term -> Bool -> IO Term
scPairSelector sc t False = scPairLeft sc t
scPairSelector sc t True = scPairRight sc t

scTupleSelector :: SharedContext -> Term -> Int -> IO Term
scTupleSelector sc t i
  | i == 1    = scPairLeft sc t
  | i > 1     = do t' <- scPairRight sc t
                   scTupleSelector sc t' (i - 1)
  | otherwise = fail "scTupleSelector: non-positive index"

scFun :: SharedContext -> Term -> Term -> IO Term
scFun sc a b = do b' <- incVars sc 0 1 b
                  scTermF sc (Pi "_" a b')

scFunAll :: SharedContext
         -> [Term]
         -> Term
         -> IO Term
scFunAll sc argTypes resultType = foldrM (scFun sc) resultType argTypes

scLambda :: SharedContext
         -> String
         -> Term
         -> Term
         -> IO Term
scLambda sc varname ty body = scTermF sc (Lambda varname ty body)

scLambdaList :: SharedContext
             -> [(String, Term)]
             -> Term
             -> IO Term
scLambdaList _ [] rhs = return rhs
scLambdaList sc ((nm,tp):r) rhs =
  scLambda sc nm tp =<< scLambdaList sc r rhs

scPi :: SharedContext
     -> String
     -> Term
     -> Term
     -> IO Term
scPi sc nm tp body = scTermF sc (Pi nm tp body)

scPiList :: SharedContext
             -> [(String, Term)]
             -> Term
             -> IO Term
scPiList _ [] rhs = return rhs
scPiList sc ((nm,tp):r) rhs = scPi sc nm tp =<< scPiList sc r rhs

scLocalVar :: SharedContext
           -> DeBruijnIndex
           -> IO Term
scLocalVar sc i = scTermF sc (LocalVar i)

scGlobalApply :: SharedContext -> Ident -> [Term] -> IO Term
scGlobalApply sc i ts =
    do c <- scGlobalDef sc i
       scApplyAll sc c ts

------------------------------------------------------------
-- Building terms using prelude functions

scBool :: SharedContext -> Bool -> IO Term
scBool sc True  = scCtorApp sc "Prelude.True" []
scBool sc False = scCtorApp sc "Prelude.False" []

scBoolType :: SharedContext -> IO Term
scBoolType sc = scDataTypeApp sc "Prelude.Bool" []

scNatType :: SharedContext -> IO Term
scNatType sc = scFlatTermF sc preludeNatType

scVecType :: SharedContext -> Term -> Term -> IO Term
scVecType sc n e =
  do vec_f <- scFlatTermF sc preludeVecTypeFun
     scApplyAll sc vec_f [n, e]

scNot :: SharedContext -> Term -> IO Term
scNot sc t = scGlobalApply sc "Prelude.not" [t]

scAnd :: SharedContext -> Term -> Term -> IO Term
scAnd sc x y = scGlobalApply sc "Prelude.and" [x,y]

scOr :: SharedContext -> Term -> Term -> IO Term
scOr sc x y = scGlobalApply sc "Prelude.or" [x,y]

scImplies :: SharedContext -> Term -> Term
          -> IO Term
scImplies sc x y = scGlobalApply sc "Prelude.implies" [x,y]

scXor :: SharedContext -> Term -> Term -> IO Term
scXor sc x y = scGlobalApply sc "Prelude.xor" [x,y]

scBoolEq :: SharedContext -> Term -> Term -> IO Term
scBoolEq sc x y = scGlobalApply sc "Prelude.boolEq" [x,y]

-- ite :: (a :: sort 1) -> Bool -> a -> a -> a;
scIte :: SharedContext -> Term -> Term ->
         Term -> Term -> IO Term
scIte sc t b x y = scGlobalApply sc "Prelude.ite" [t, b, x, y]

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
scAppend :: SharedContext -> Term -> Term -> Term ->
            Term -> Term -> IO Term
scAppend sc t m n x y = scGlobalApply sc "Prelude.append" [m, n, t, x, y]

-- | slice :: (e :: sort 1) -> (i n o :: Nat) -> Vec (addNat (addNat i n) o) e -> Vec n e;
scSlice :: SharedContext -> Term -> Term ->
           Term -> Term -> Term -> IO Term
scSlice sc e i n o a = scGlobalApply sc "Prelude.slice" [e, i, n, o, a]

-- | get :: (n :: Nat) -> (e :: sort 0) -> Vec n e -> Fin n -> e;
scGet :: SharedContext -> Term -> Term ->
         Term -> Term -> IO Term
scGet sc n e v i = scGlobalApply sc (mkIdent preludeName "get") [n, e, v, i]

-- | bvAt :: (n :: Nat) -> (a :: sort 0) -> (i :: Nat) -> Vec n a -> bitvector i -> a;
scBvAt :: SharedContext -> Term -> Term ->
         Term -> Term -> Term -> IO Term
scBvAt sc n a i xs idx = scGlobalApply sc (mkIdent preludeName "bvAt") [n, a, i, xs, idx]

-- | at :: (n :: Nat) -> (a :: sort 0) -> Vec n a -> Nat -> a;
scAt :: SharedContext -> Term -> Term ->
        Term -> Term -> IO Term
scAt sc n a xs idx = scGlobalApply sc (mkIdent preludeName "at") [n, a, xs, idx]

-- | single :: (e :: sort 1) -> e -> Vec 1 e;
-- single e x = generate 1 e (\(i :: Fin 1) -> x);
scSingle :: SharedContext -> Term -> Term -> IO Term
scSingle sc e x = scGlobalApply sc (mkIdent preludeName "single") [e, x]

scLsb :: SharedContext -> Term -> Term -> IO Term
scLsb sc n x = scGlobalApply sc (mkIdent preludeName "lsb") [n, x]

scMsb :: SharedContext -> Term -> Term -> IO Term
scMsb sc n x = scGlobalApply sc (mkIdent preludeName "lsb") [n, x]

-- Primitive operations on nats

scAddNat :: SharedContext -> Term -> Term -> IO Term
scAddNat sc x y = scGlobalApply sc "Prelude.addNat" [x,y]

scSubNat :: SharedContext -> Term -> Term -> IO Term
scSubNat sc x y = scGlobalApply sc "Prelude.subNat" [x,y]

scMulNat :: SharedContext -> Term -> Term -> IO Term
scMulNat sc x y = scGlobalApply sc "Prelude.mulNat" [x,y]

scEqualNat :: SharedContext -> Term -> Term -> IO Term
scEqualNat sc x y = scGlobalApply sc "Prelude.equalNat" [x,y]

scLtNat :: SharedContext -> Term -> Term -> IO Term
scLtNat sc x y = scGlobalApply sc "Prelude.ltNat" [x,y]

scMinNat :: SharedContext -> Term -> Term -> IO Term
scMinNat sc x y = scGlobalApply sc "Prelude.minNat" [x,y]

scMaxNat :: SharedContext -> Term -> Term -> IO Term
scMaxNat sc x y = scGlobalApply sc "Prelude.maxNat" [x,y]

-- Primitive operations on Integer

scIntegerType :: SharedContext -> IO Term
scIntegerType sc = scFlatTermF sc preludeIntegerType

-- primitive intAdd/intSub/intMul/intDiv/intMod :: Integer -> Integer -> Integer;
scIntAdd, scIntSub, scIntMul, scIntDiv, scIntMod, scIntMax, scIntMin
   :: SharedContext -> Term -> Term -> IO Term
scIntAdd sc x y = scGlobalApply sc "Prelude.intAdd" [x, y]
scIntSub sc x y = scGlobalApply sc "Prelude.intSub" [x, y]
scIntMul sc x y = scGlobalApply sc "Prelude.intMul" [x, y]
scIntDiv sc x y = scGlobalApply sc "Prelude.intDiv" [x, y]
scIntMod sc x y = scGlobalApply sc "Prelude.intMod" [x, y]
scIntMin sc x y = scGlobalApply sc "Prelude.intMin" [x, y]
scIntMax sc x y = scGlobalApply sc "Prelude.intMax" [x, y]

-- primitive intNeg :: Integer -> Integer;
scIntNeg
   :: SharedContext -> Term -> IO Term
scIntNeg sc x = scGlobalApply sc "Prelude.intNeg" [x]

-- primitive intEq/intLe/intLt  :: Integer -> Integer -> Bool;
scIntEq, scIntLe, scIntLt
   :: SharedContext -> Term -> Term -> IO Term
scIntEq sc x y = scGlobalApply sc "Prelude.intEq" [x, y]
scIntLe sc x y = scGlobalApply sc "Prelude.intLe" [x, y]
scIntLt sc x y = scGlobalApply sc "Prelude.intLt" [x, y]

-- primitive intToNat :: Integer -> Nat;
scIntToNat
   :: SharedContext -> Term -> IO Term
scIntToNat sc x = scGlobalApply sc "Prelude.intToNat" [x]

-- primitive natToInt :: Nat -> Integer;
scNatToInt
   :: SharedContext -> Term -> IO Term
scNatToInt sc x = scGlobalApply sc "Prelude.natToInt" [x]

-- primitive intToBv :: (n::Nat) -> Integer -> bitvector n;
scIntToBv
   :: SharedContext -> Term -> Term -> IO Term
scIntToBv sc n x = scGlobalApply sc "Prelude.intToBv" [n,x]

-- primitive bvToInt :: (n::Nat) -> bitvector n -> Integer;
scBvToInt
   :: SharedContext -> Term -> Term -> IO Term
scBvToInt sc n x = scGlobalApply sc "Prelude.bvToInt" [n,x]

-- primitive sbvToInt :: (n::Nat) -> bitvector n -> Integer;
scSbvToInt
   :: SharedContext -> Term -> Term -> IO Term
scSbvToInt sc n x = scGlobalApply sc "Prelude.sbvToInt" [n,x]


-- Primitive operations on bitvectors

-- | bitvector :: (n : Nat) -> sort 1
-- bitvector n = Vec n Bool
scBitvector :: SharedContext -> Nat -> IO Term
scBitvector sc size = do
  c <- scGlobalDef sc "Prelude.bitvector"
  s <- scNat sc size
  scApply sc c s

-- | bvNat :: (x :: Nat) -> Nat -> bitvector x;
scBvNat :: SharedContext -> Term -> Term -> IO Term
scBvNat sc x y = scGlobalApply sc "Prelude.bvNat" [x, y]

-- bvToNat :: (n :: Nat) -> bitvector n -> Nat;
scBvToNat :: SharedContext -> Nat -> Term -> IO Term
scBvToNat sc n x = do
    n' <- scNat sc n
    scGlobalApply sc "Prelude.bvToNat" [n',x]

-- | Returns constant bitvector.
scBvConst :: SharedContext -> Nat -> Integer -> IO Term
scBvConst sc w v = assert (w <= fromIntegral (maxBound :: Int)) $ do
  x <- scNat sc w
  y <- scNat sc $ fromInteger $ v .&. (1 `shiftL` fromIntegral w - 1)
  scGlobalApply sc "Prelude.bvNat" [x, y]

-- | FinVal :: (x r :: Nat) -> Fin (Succ (addNat r x));
scFinVal :: SharedContext -> Term -> Term -> IO Term
scFinVal sc a b = scCtorApp sc "Prelude.FinVal" [a, b]

-- | bvBool :: (n :: Nat) -> Bool -> bitvector n;
scBvBool :: SharedContext -> Term -> Term -> IO Term
scBvBool sc n x = scGlobalApply sc "Prelude.bvBool" [n, x]

-- | bvNonzero :: (n :: Nat) -> bitvector n -> Bool;
scBvNonzero :: SharedContext -> Term -> Term -> IO Term
scBvNonzero sc n x = scGlobalApply sc "Prelude.bvNonzero" [n, x]

-- | bvNeg :: (x::Nat) -> bitvector x -> bitvector x;
scBvNeg :: SharedContext -> Term -> Term -> IO Term
scBvNeg sc n x = scGlobalApply sc "Prelude.bvNeg" [n, x]

-- | bvAdd/Sub/Mul :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
scBvAdd, scBvSub, scBvMul, scBvURem, scBvUDiv, scBvSRem, scBvSDiv
    :: SharedContext -> Term -> Term -> Term -> IO Term
scBvAdd sc n x y = scGlobalApply sc "Prelude.bvAdd" [n, x, y]
scBvSub sc n x y = scGlobalApply sc "Prelude.bvSub" [n, x, y]
scBvMul sc n x y = scGlobalApply sc "Prelude.bvMul" [n, x, y]
scBvURem sc n x y = scGlobalApply sc "Prelude.bvURem" [n, x, y]
scBvUDiv sc n x y = scGlobalApply sc "Prelude.bvUDiv" [n, x, y]
scBvSRem sc n x y = scGlobalApply sc "Prelude.bvSRem" [n, x, y]
scBvSDiv sc n x y = scGlobalApply sc "Prelude.bvSDiv" [n, x, y]

-- | bvOr/And/Xor :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n;
scBvOr, scBvAnd, scBvXor
    :: SharedContext -> Term -> Term -> Term -> IO Term
scBvAnd sc n x y = scGlobalApply sc "Prelude.bvAnd" [n, x, y]
scBvXor sc n x y = scGlobalApply sc "Prelude.bvXor" [n, x, y]
scBvOr  sc n x y = scGlobalApply sc "Prelude.bvOr"  [n, x, y]

-- | bvNot :: (n :: Nat) -> bitvector n -> bitvector n;
scBvNot :: SharedContext -> Term -> Term -> IO Term
scBvNot sc n x = scGlobalApply sc "Prelude.bvNot" [n, x]

-- | bvEq :: (n :: Nat) -> bitvector n -> bitvector n -> Bool;
scBvEq, scBvUGe, scBvUGt, scBvULe, scBvULt
    :: SharedContext -> Term -> Term -> Term -> IO Term
scBvEq  sc n x y = scGlobalApply sc "Prelude.bvEq"  [n, x, y]
scBvUGe sc n x y = scGlobalApply sc "Prelude.bvuge" [n, x, y]
scBvULe sc n x y = scGlobalApply sc "Prelude.bvule" [n, x, y]
scBvUGt sc n x y = scGlobalApply sc "Prelude.bvugt" [n, x, y]
scBvULt sc n x y = scGlobalApply sc "Prelude.bvult" [n, x, y]


-- | bvsgt/bvsge/bvslt/bvsle :: (n :: Nat) -> bitvector n -> bitvector n -> Bool;
scBvSGt, scBvSGe, scBvSLt, scBvSLe
    :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSGe sc n x y = scGlobalApply sc "Prelude.bvsge" [n, x, y]
scBvSLe sc n x y = scGlobalApply sc "Prelude.bvsle" [n, x, y]
scBvSGt sc n x y = scGlobalApply sc "Prelude.bvsgt" [n, x, y]
scBvSLt sc n x y = scGlobalApply sc "Prelude.bvslt" [n, x, y]

-- | bvShl, bvShr :: (n :: Nat) -> bitvector n -> Nat -> bitvector n;
scBvShl, scBvShr
    :: SharedContext -> Term -> Term -> Term -> IO Term
scBvShl sc n x y = scGlobalApply sc "Prelude.bvShl" [n, x, y]
scBvShr sc n x y = scGlobalApply sc "Prelude.bvShr" [n, x, y]

-- | bvSShr :: (w :: Nat) -> bitvector (Succ w) -> Nat -> bitvector (Succ w);
scBvSShr :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSShr sc n x y = scGlobalApply sc "Prelude.bvSShr" [n, x, y]

-- | bvUExt :: (x y :: Nat) -> bitvector y -> bitvector (addNat x y);
scBvUExt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvUExt sc n m x = scGlobalApply sc "Prelude.bvUExt" [n,m,x]

-- | bvSExt :: (x y :: Nat) -> bitvector (Succ y) -> bitvector (addNat x (Succ y));
scBvSExt :: SharedContext -> Term -> Term -> Term -> IO Term
scBvSExt sc n m x = scGlobalApply sc "Prelude.bvSExt" [n,m,x]

-- | bvTrunc :: (x y :: Nat) -> bitvector (addNat x y) -> bitvector y;
scBvTrunc :: SharedContext -> Term -> Term -> Term -> IO Term
scBvTrunc sc n m x = scGlobalApply sc "Prelude.bvTrunc" [n,m,x]

-- | updNatFun :: (a::sort 0) -> (Nat -> a) -> Nat -> a -> (Nat -> a);
scUpdNatFun :: SharedContext -> Term -> Term
            -> Term -> Term -> IO Term
scUpdNatFun sc a f i v = scGlobalApply sc "Prelude.updNatFun" [a, f, i, v]

-- | updBvFun :: (n::Nat) -> (a::sort 0) -> (bitvector n -> a) -> bitvector n -> a -> (bitvector n -> a);
scUpdBvFun :: SharedContext -> Term -> Term
           -> Term -> Term -> Term -> IO Term
scUpdBvFun sc n a f i v = scGlobalApply sc "Prelude.updBvFun" [n, a, f, i, v]

------------------------------------------------------------
-- | The default instance of the SharedContext operations.
mkSharedContext :: Module -> IO SharedContext
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
getAllExts :: Term -> [ExtCns Term]
getAllExts t = Set.toList (getAllExtSet t)

-- | Return a set of all ExtCns subterms in the given term.
--   Does not traverse the unfoldings of @Constant@ terms.
getAllExtSet :: Term -> Set.Set (ExtCns Term)
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

getConstantSet :: Term -> Map String (Term, Term)
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
scInstantiateExt :: SharedContext
                 -> Map VarIndex Term
                 -> Term
                 -> IO Term
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
  let go :: Term -> ChangeT IO Term
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
scAbstractExts :: SharedContext -> [ExtCns Term] -> Term -> IO Term
scAbstractExts _ [] x = return x
scAbstractExts sc exts x =
   do ls <- sequence [ scTermF sc (LocalVar db) >>= \t -> return ( ecVarIndex ec, t )
                     | ec <- reverse exts
                     | db <- [0 .. ]
                     ]
      let m = Map.fromList ls
      let lams = [ ( ecName ec, ecType ec ) | ec <- exts ]
      scLambdaList sc lams =<< scInstantiateExt sc m x


scUnfoldConstants :: SharedContext -> [String] -> Term -> IO Term
scUnfoldConstants sc names t0 = scUnfoldConstantSet sc True (Set.fromList names) t0

-- | TODO: test whether this version is slower or faster.
scUnfoldConstants' :: SharedContext -> [String] -> Term -> IO Term
scUnfoldConstants' sc names t0 = scUnfoldConstantSet' sc True (Set.fromList names) t0

scUnfoldConstantSet :: SharedContext
                    -> Bool  -- ^ True: unfold constants in set. False: unfold constants NOT in set
                    -> Set String -- ^ Set of constant names
                    -> Term
                    -> IO Term
scUnfoldConstantSet sc b names t0 = do
  cache <- newCache
  let go :: Term -> IO Term
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
scUnfoldConstantSet' :: SharedContext
                    -> Bool  -- ^ True: unfold constants in set. False: unfold constants NOT in set
                    -> Set String -- ^ Set of constant names
                    -> Term
                    -> IO Term
scUnfoldConstantSet' sc b names t0 = do
  tcache <- newCacheMap' Map.empty
  let go :: Term -> ChangeT IO Term
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


-- | Return the number of DAG nodes used by the given @Term@.
scSharedSize :: Term -> Integer
scSharedSize = fst . go (0, Set.empty)
  where
    go (sz, seen) (Unshared tf) = foldl' go (strictPair (sz + 1) seen) tf
    go (sz, seen) (STApp{ stAppIndex = idx, stAppTermF = tf })
      | Set.member idx seen = (sz, seen)
      | otherwise = foldl' go (strictPair (sz + 1) (Set.insert idx seen)) tf

strictPair :: a -> b -> (a, b)
strictPair x y = x `seq` y `seq` (x, y)

-- | Return the number of nodes that would be used by the given
-- @Term@ if it were represented as a tree instead of a DAG.
scTreeSize :: Term -> Integer
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
scOpenTerm :: SharedContext
         -> String
         -> Term
         -> DeBruijnIndex
         -> Term
         -> IO (ExtCns Term, Term)
scOpenTerm sc nm tp idx body = do
    v <- scFreshGlobalVar sc
    let ec = EC v nm tp
    ec_term <- scFlatTermF sc (ExtCns ec)
    body' <- instantiateVar sc idx ec_term body
    return (ec, body')

-- | `closeTerm closer sc ec body` replaces the external constant `ec` in `body` by
--   a new deBruijn variable and binds it using the binding form given by 'close'.
--   The name and type of the new bound variable are given by the name and type of `ec`.
scCloseTerm :: (SharedContext -> String -> Term -> Term -> IO Term)
          -> SharedContext
          -> ExtCns Term
          -> Term
          -> IO Term
scCloseTerm close sc ec body = do
    lv <- scLocalVar sc 0
    body' <- scInstantiateExt sc (Map.insert (ecVarIndex ec) lv Map.empty) =<< incVars sc 0 1 body
    close sc (ecName ec) (ecType ec) body'
