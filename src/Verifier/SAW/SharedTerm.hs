{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
module Verifier.SAW.SharedTerm
  ( TermF(..)
  , Ident, mkIdent
  , SharedTerm(..)
  , VarIndex
  , TermIndex
  , Termlike(..)
  , looseVars
  , unshare
    -- * SharedContext interface for building shared terms
  , SharedContext
  , mkSharedContext
    -- ** Low-level generic term constructors
  , scTermF
  , scFlatTermF
    -- ** Implicit versions of functions.
  , scDefTerm
  , scFreshGlobal
  , scGlobalDef
  , scModule
  , scApply
  , scApplyAll
  , scMkRecord
  , scRecordSelect
  , scRecordType
  , scDataTypeApp
  , scCtorApp
  , scApplyCtor
  , scFun
  , scNat
  , scNatType
  , scBoolType
  , scFunAll
  , scLambda
  , scLocalVar
  , scLookupDef
  , scTuple
  , scTupleType
  , scTupleSelector
  , scTermCount
  , scPrettyTerm
  , scPrettyTermDoc
  , scViewAsBool
  , scViewAsNum
  , scGlobalApply
  , scSharedTerm
    -- ** Type checking
  , scTypeOf
  , scTypeOfGlobal
    -- ** Prelude operations
  , scAppend
  , scIte
  , scSlice
    -- *** Bitvector primitives
  , scBitvector
  , scBvNat
  , scBvAdd, scBvSub, scBvMul
  , scBvOr, scBvAnd, scBvXor
  , scBvNot
  , scBvEq, scBvUGe, scBvUGt, scBvULe, scBvULt
  , scBvShl, scBvShr
    -- ** Utilities
--  , scTrue
--  , scFalse
    -- ** Variable substitution
  , instantiateVar
  , instantiateVarList
  , asTermF
  , asNatLit
  ) where

import Control.Applicative
-- ((<$>), pure, (<*>))
import Control.Concurrent.MVar
import Control.Lens
import Control.Monad (foldM, liftM, when)
import Control.Monad.State.Strict as State
import Control.Monad.Trans (lift)
import Data.Bits
import Data.Hashable (Hashable(..), hash)
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import qualified Data.IntMap.Strict as IMap

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Word
import Data.Foldable hiding (sum)
import Data.Traversable ()
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.Leijen hiding ((<$>))

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.TypedAST hiding (incVars, instantiateVarList)

type TermIndex = Int -- Word64

data SharedTerm s
  = STApp !TermIndex !(TermF (SharedTerm s))

instance Hashable (SharedTerm s) where
    hashWithSalt x (STApp idx _) = hashWithSalt x idx

instance Eq (SharedTerm s) where
  STApp x _ == STApp y _ = x == y

instance Ord (SharedTerm s) where
  compare (STApp x _) (STApp y _) = compare x y

class Termlike t where
  unwrapTermF :: t -> TermF t

instance Termlike Term where
  unwrapTermF (Term tf) = tf

instance Termlike (SharedTerm s) where
  unwrapTermF (STApp _ tf) = tf

----------------------------------------------------------------------
-- SharedContext: a high-level interface for building SharedTerms.

data SharedContext s = SharedContext
  { -- | Returns the current module for the underlying global theory.
    scModule        :: IO Module
  , scTermF         :: TermF (SharedTerm s) -> IO (SharedTerm s)
    -- | Create a global variable with the given identifier (which may be "_") and type.
  , scFreshGlobal   :: String -> SharedTerm s -> IO (SharedTerm s)
  }

scFlatTermF :: SharedContext s -> FlatTermF (SharedTerm s) -> IO (SharedTerm s)
scFlatTermF sc ftf = scTermF sc (FTermF ftf)

-- | Returns shared term associated with ident.
-- Does not check module namespace.
scGlobalDef :: SharedContext s -> Ident -> IO (SharedTerm s)
scGlobalDef sc ident = scFlatTermF sc (GlobalDef ident)

scApply :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scApply sc f = scFlatTermF sc . App f

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scDataTypeApp :: SharedContext s -> Ident -> [SharedTerm s] -> IO (SharedTerm s)
scDataTypeApp sc ident args = scFlatTermF sc (DataTypeApp ident args)

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scCtorApp :: SharedContext s -> Ident -> [SharedTerm s] -> IO (SharedTerm s)
scCtorApp sc ident args = scFlatTermF sc (CtorApp ident args)

-- SharedContext implementation.

data AppCache s = AC { acBindings :: !(HashMap (TermF (SharedTerm s)) (SharedTerm s))
                     , acNextIdx :: !TermIndex
                     }

type AppCacheRef s = MVar (AppCache s)

emptyAppCache :: AppCache s
emptyAppCache = AC HMap.empty 0

instance Show (TermF (SharedTerm s)) where
  show t@FTermF{} = "termF fTermF"
  show _ = "termF SharedTerm"

-- | Return term for application using existing term in cache if it is avaiable.
getTerm :: AppCacheRef s -> TermF (SharedTerm s) -> IO (SharedTerm s)
getTerm r a =
  modifyMVar r $ \s -> do
    case HMap.lookup a (acBindings s) of
      Just t -> return (s,t)
      Nothing -> do
          seq s' $ return (s',t)
        where t = STApp (acNextIdx s) a
              s' = s { acBindings = HMap.insert a t (acBindings s)
                     , acNextIdx = acNextIdx s + 1
                     }

-- | Substitute var 0 in first term for second term, and shift all variable
-- references down.
subst0 :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
subst0 sc t t0 = instantiateVar sc 0 t0 t

reducePi :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
reducePi sc (STApp _ (Pi _ _ body)) arg = instantiateVar sc 0 arg body
reducePi _ _ _ = error "reducePi: not a Pi term"

scTypeOfGlobal :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfGlobal sc ident =
    do m <- scModule sc
       case findDef m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm sc (defType d)

scTypeOfDataType :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfDataType sc ident =
    do m <- scModule sc
       case findDataType m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm sc (dtType d)

scTypeOfCtor :: SharedContext s -> Ident -> IO (SharedTerm s)
scTypeOfCtor sc ident =
    do m <- scModule sc
       case findCtor m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm sc (ctorType d)

-- TODO: separate versions of typeOf: One fast one that assumes the
-- term is well-formed. Another that completely typechecks a term,
-- ensuring that it is well-formed. The full typechecking should use
-- memoization on subterms. Perhaps the fast one won't need to?

scTypeOf :: forall s. SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scTypeOf sc t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: SharedTerm s -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    memo (STApp i t) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          x <- termf t
          State.modify (Map.insert i x)
          return x
    sort :: SharedTerm s -> State.StateT (Map TermIndex (SharedTerm s)) IO Sort
    sort t = do
      STApp _ (FTermF (Sort s)) <- memo t
      return s
    termf :: TermF (SharedTerm s) -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    termf tf =
      case tf of
        FTermF ftf -> ftermf ftf
        Lambda (PVar i _ _) tp rhs -> do
          rtp <- memo rhs
          lift $ scTermF sc (Pi i tp rtp)
        Pi _ tp rhs -> do
          ltp <- sort tp
          rtp <- sort rhs
          lift $ scSort sc (max ltp rtp)
        Let defs rhs -> undefined defs rhs
        LocalVar _ tp -> return tp
    ftermf :: FlatTermF (SharedTerm s)
           -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    ftermf tf =
      case tf of
        GlobalDef d -> lift $ scTypeOfGlobal sc d
        App x y -> do
          tx <- memo x
          lift $ reducePi sc tx y
        TupleValue l -> lift . scTupleType sc =<< traverse memo l
        TupleType l -> lift . scSort sc . maximum =<< traverse sort l
        TupleSelector t i -> do
          STApp _ (FTermF (TupleType ts)) <- memo t
          return (ts !! (i-1)) -- FIXME test for i < length ts
        RecordValue m -> lift . scRecordType sc =<< traverse memo m
        RecordSelector t f -> do
          STApp _ (FTermF (RecordType m)) <- memo t
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
        NatLit i -> lift $ scNatType sc
        ArrayValue tp _ -> error "typeOfFTermF ArrayValue" tp
        FloatLit{}  -> lift $ scFlatTermF sc (DataTypeApp preludeFloatIdent  [])
        DoubleLit{} -> lift $ scFlatTermF sc (DataTypeApp preludeDoubleIdent [])

-- | The inverse function to @sharedTerm@.
unshare :: forall s. SharedTerm s -> Term
unshare t = State.evalState (go t) Map.empty
  where
    go :: SharedTerm s -> State.State (Map TermIndex Term) Term
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

sharedTerm :: MVar (AppCache s) -> Term -> IO (SharedTerm s)
sharedTerm mvar = go
    where go (Term termf) = getTerm mvar =<< traverse go termf

scSharedTerm :: SharedContext s -> Term -> IO (SharedTerm s)
scSharedTerm sc = go
    where go (Term termf) = scTermF sc =<< traverse go termf

-- | Returns bitset containing indices of all free local variables.
looseVars :: forall s. SharedTerm s -> BitSet
looseVars t = State.evalState (go t) Map.empty
    where
      go :: SharedTerm s -> State.State (Map TermIndex BitSet) BitSet
      go (STApp i tf) = do
        memo <- State.get
        case Map.lookup i memo of
          Just x -> return x
          Nothing -> do
            x <- freesTermF <$> traverse go tf
            State.modify (Map.insert i x)
            return x

instantiateVars :: forall s. SharedContext s
                -> (DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
                                  -> ChangeT IO (IO (SharedTerm s)))
                -> DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
instantiateVars sc f initialLevel t =
    do cache <- lift newCache
       let ?cache = cache in go initialLevel t
  where
    go :: (?cache :: Cache IO (TermIndex, DeBruijnIndex) (Change (SharedTerm s))) =>
          DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
    go l t@(STApp tidx tf) =
        ChangeT $ useCache ?cache (tidx, l) (runChangeT $ preserveChangeT t (go' l tf))

    go' :: (?cache :: Cache IO (TermIndex, DeBruijnIndex) (Change (SharedTerm s))) =>
           DeBruijnIndex -> TermF (SharedTerm s) -> ChangeT IO (IO (SharedTerm s))
    go' l (FTermF tf) = scFlatTermF sc <$> (traverse (go l) tf)
    go' l (Lambda i tp rhs) = scTermF sc <$> (Lambda i <$> go l tp <*> go (l+1) rhs)
    go' l (Pi i lhs rhs)    = scTermF sc <$> (Pi i <$> go l lhs <*> go (l+1) rhs)
    go' l (Let defs r) = scTermF sc <$> (Let <$> changeList procDef defs <*> go l' r)
      where l' = l + length defs
            procDef :: LocalDef (SharedTerm s) -> ChangeT IO (LocalDef (SharedTerm s))
            procDef (LocalFnDef sym tp eqs) =
              LocalFnDef sym <$> go l tp <*> changeList procEq eqs
            procEq :: DefEqn (SharedTerm s) -> ChangeT IO (DefEqn (SharedTerm s))
            procEq (DefEqn pats rhs) = DefEqn pats <$> go eql rhs
              where eql = l' + sum (patBoundVarCount <$> pats)
    go' l (LocalVar i tp)
      | i < l     = scTermF sc <$> (LocalVar i <$> go (l-(i+1)) tp)
      | otherwise = f l i (go (l-(i+1)) tp)

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVarsChangeT :: SharedContext s
               -> DeBruijnIndex -> DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
incVarsChangeT sc initialLevel j
    | j == 0 = return
    | j >  0 = instantiateVars sc fn initialLevel
    where
      fn _ i t = taint $ scTermF sc <$> (LocalVar (i+j) <$> t)

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
        term :: (?cache :: Cache (ChangeT IO) DeBruijnIndex (SharedTerm s)) =>
                DeBruijnIndex -> ChangeT IO (SharedTerm s)
        term i = useCache ?cache i (incVarsChangeT sc 0 i t0)
        -- Instantiate variable 0.
        fn :: (?cache :: Cache (ChangeT IO) DeBruijnIndex (SharedTerm s)) =>
              DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
                            -> ChangeT IO (IO (SharedTerm s))
        fn i j t | j  > i + k = taint $ scTermF sc <$> (LocalVar (j - 1) <$> t)
                 | j == i + k = taint $ return <$> term i
                 | otherwise  = scTermF sc <$> (LocalVar j <$> t)

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
    term :: (Cache (ChangeT IO) DeBruijnIndex (SharedTerm s), SharedTerm s)
         -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
    term (cache, t) i = useCache cache i (incVarsChangeT sc 0 i t)
    -- Instantiate variables [k .. k+l-1].
    fn :: [(Cache (ChangeT IO) DeBruijnIndex (SharedTerm s), SharedTerm s)]
       -> DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
       -> ChangeT IO (IO (SharedTerm s))
    fn rs i j t | j >= i + k + l = taint $ scTermF sc <$> (LocalVar (j - l) <$> t)
                | j >= i + k     = taint $ return <$> term (rs !! (j - i - k)) i
                | otherwise      = scTermF sc <$> (LocalVar j <$> t)

instantiateVarList :: SharedContext s
                   -> DeBruijnIndex -> [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
instantiateVarList sc k ts t = commitChangeT (instantiateVarListChangeT sc k ts t)

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

scNat :: SharedContext s -> Integer -> IO (SharedTerm s)
scNat sc n
  | 0 <= n = scFlatTermF sc (NatLit n)
  | otherwise = error $ "scNat: negative value " ++ show n

scMkRecord :: SharedContext s -> Map FieldName (SharedTerm s) -> IO (SharedTerm s)
scMkRecord sc m = scFlatTermF sc (RecordValue m)

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

type OccurenceMap = IMap.IntMap Word64

-- | Returns map that associated each term index appearing in the term
-- to the number of occurences in the shared term.
scTermCount :: SharedTerm s -> OccurenceMap
scTermCount t0 = execState (rec [t0]) IMap.empty
  where rec :: [SharedTerm s] -> State OccurenceMap ()
        rec [] = return ()
        rec (STApp i tf:r) = do
          m <- get
          case IMap.lookup (fromIntegral i) m of
            Just n -> do
              put $ IMap.insert (fromIntegral i) (n+1) m
              rec r
            Nothing -> do
              put $ IMap.insert (fromIntegral i) 1 m              
              rec (Data.Foldable.foldr' (:) r tf)

ppTermF' :: Applicative f
         => (LocalVarDoc -> Prec -> SharedTerm s -> f Doc)
         -> LocalVarDoc
         -> Prec
         -> TermF (SharedTerm s)
         -> f Doc
ppTermF' pp lcls p t0 =
  case t0 of
    FTermF tf ->
      case tf of
        GlobalDef i -> pure (ppIdent i)
        App x y -> ppParens (p >= 10) <$> liftA2 (<+>) (pp lcls 10 x) (pp lcls 10 y)
        ExtCns ec -> pure (text (ecName ec))

scPrettyTermDoc :: SharedTerm s -> Doc
scPrettyTermDoc t0 = evalState (go emptyLocalVarDoc 0 t0) IMap.empty
  where ocm = scTermCount t0 -- Occurence map
        go :: LocalVarDoc
           -> Prec
           -> SharedTerm s
           -> State (IMap.IntMap Doc) Doc
        go lcls p (STApp i tf) = do
          md <- IMap.lookup (fromIntegral i) <$> get
          case md of
            Just d -> return d
            Nothing 
              | shouldShare -> do
                  d <- ppTermF' go lcls 11 tf
                  m <- get
                  let v = text $ 'x' : show (IMap.size m)
                  put $ IMap.insert (fromIntegral i) v m
                  return $ v <> text "@" <> d
              | otherwise -> ppTermF' go lcls p tf
             where Just c = IMap.lookup (fromIntegral i) ocm
                   shouldShare = c >= 2

scPrettyTerm :: SharedTerm s -> String
scPrettyTerm t = show (scPrettyTermDoc t)

scFun :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scFun sc a b = do b' <- incVars sc 0 1 b
                  scTermF sc (Pi "_" a b')

scFunAll :: SharedContext s -> [SharedTerm s] -> SharedTerm s -> IO (SharedTerm s)
scFunAll sc argTypes resultType = foldrM (scFun sc) resultType argTypes

scLambda :: SharedContext s -> String -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scLambda sc varname ty body = scTermF sc (Lambda (PVar varname 0 ty) ty body)

scLocalVar :: SharedContext s -> DeBruijnIndex -> SharedTerm s -> IO (SharedTerm s)
scLocalVar sc i t = scTermF sc (LocalVar i t)

scGlobalApply :: SharedContext s -> Ident -> [SharedTerm s] -> IO (SharedTerm s)
scGlobalApply sc i ts =
    do c <- scGlobalDef sc i
       scApplyAll sc c ts

------------------------------------------------------------
-- Building terms using prelude functions

scBoolType :: SharedContext s -> IO (SharedTerm s)
scBoolType sc = scFlatTermF sc (DataTypeApp (mkIdent preludeModuleName "Bool") [])

scNatType :: SharedContext s -> IO (SharedTerm s)
scNatType sc = scFlatTermF sc (DataTypeApp preludeNatIdent [])

-- ite :: (a :: sort 1) -> Bool -> a -> a -> a;
scIte :: SharedContext s -> SharedTerm s -> SharedTerm s ->
         SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scIte sc t b x y = scGlobalApply sc (mkIdent preludeName "ite") [t, b, x, y]

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
scAppend :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s ->
            SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scAppend sc t m n x y = scGlobalApply sc (mkIdent preludeName "append") [m, n, t, x, y]

-- | slice :: (e :: sort 1) -> (i n o :: Nat) -> Vec (addNat (addNat i n) o) e -> Vec n e;
scSlice :: SharedContext s -> SharedTerm s -> SharedTerm s ->
           SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scSlice sc e i n o a = scGlobalApply sc (mkIdent preludeName "slice") [e, i, n, o, a]

-- Primitive operations on bitvectors

-- | bitvector :: (n : Nat) -> sort 1
-- bitvector n = Vec n Bool
scBitvector :: SharedContext s -> Integer -> IO (SharedTerm s)
scBitvector sc size =
    do s <- scNat sc size
       c <- scGlobalDef sc (mkIdent preludeName "bitvector")
       scApply sc c s

-- | bvNat :: (x :: Nat) -> Nat -> bitvector x;
scBvNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvNat sc x y = scGlobalApply sc (mkIdent preludeName "bvNat") [x, y]

-- | bvAdd/Sub/Mul :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
scBvAdd, scBvSub, scBvMul
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvAdd sc n x y = scGlobalApply sc (mkIdent preludeName "bvAdd") [n, x, y]
scBvSub sc n x y = scGlobalApply sc (mkIdent preludeName "bvSub") [n, x, y]
scBvMul sc n x y = scGlobalApply sc (mkIdent preludeName "bvMul") [n, x, y]

-- | bvOr/And/Xor :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n;
scBvOr, scBvAnd, scBvXor
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvAnd sc n x y = scGlobalApply sc (mkIdent preludeName "bvAnd") [n, x, y]
scBvXor sc n x y = scGlobalApply sc (mkIdent preludeName "bvXor") [n, x, y]
scBvOr sc n x y = scGlobalApply sc (mkIdent preludeName "bvOr") [n, x, y]

-- | bvNot :: (n :: Nat) -> bitvector n -> bitvector n;
scBvNot :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvNot sc n x = scGlobalApply sc (mkIdent preludeName "bvNot") [n, x]

-- | bvEq :: (n :: Nat) -> bitvector n -> bitvector n -> Bool;
scBvEq, scBvUGe, scBvUGt, scBvULe, scBvULt
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvEq sc n x y = scGlobalApply sc (mkIdent preludeName "bvEq") [n, x, y]
scBvUGe sc n x y = scGlobalApply sc (mkIdent preludeName "bvuge") [n, x, y]
scBvULe sc n x y = scGlobalApply sc (mkIdent preludeName "bvule") [n, x, y]
scBvUGt sc n x y = scGlobalApply sc (mkIdent preludeName "bvugt") [n, x, y]
scBvULt sc n x y = scGlobalApply sc (mkIdent preludeName "bvult") [n, x, y]

-- | bvShl, bvShr :: (n :: Nat) -> bitvector n -> Nat -> bitvector n;
scBvShl, scBvShr
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvShl sc n x y = scGlobalApply sc (mkIdent preludeName "bvShl") [n, x, y]
scBvShr sc n x y = scGlobalApply sc (mkIdent preludeName "bvShr") [n, x, y]

------------------------------------------------------------
-- | The default instance of the SharedContext operations.
mkSharedContext :: Module -> IO (SharedContext s)
mkSharedContext m = do
  vr <- newMVar  0 -- ^ Reference for getting variables.
  cr <- newMVar emptyAppCache
--  let shareDef d = do
--        t <- sharedTerm cr $ Term (FTermF (GlobalDef (defIdent d)))
--        return (defIdent d, t)
--  sharedDefMap <- Map.fromList <$> traverse shareDef (moduleDefs m)
--  let getDef sym =
--        case Map.lookup (mkIdent (moduleName m) sym) sharedDefMap of
--          Nothing -> fail $ "Failed to find " ++ show sym ++ " in module."
--          Just d -> return d
  let freshGlobal sym tp = do
        i <- modifyMVar vr (\i -> return (i+1,i))
        getTerm cr (FTermF (ExtCns (EC i sym tp)))
  return SharedContext {
             scModule = return m
           , scTermF = getTerm cr
           , scFreshGlobal = freshGlobal
           }

asTermF :: SharedTerm s -> Maybe (TermF (SharedTerm s))
asTermF (STApp _ app) = Just app
asTermF _ = Nothing

asFTermF :: SharedTerm s -> Maybe (FlatTermF (SharedTerm s))
asFTermF t = do FTermF ftf <- asTermF t; return ftf

asNatLit :: SharedTerm s -> Maybe Integer
asNatLit t = do NatLit i <- asFTermF t; return i

asApp :: SharedTerm s -> Maybe (SharedTerm s, SharedTerm s)
asApp t = do App x y <- asFTermF t; return (x,y)

asApp3Of :: SharedTerm s -> SharedTerm s -> Maybe (SharedTerm s, SharedTerm s, SharedTerm s)
asApp3Of op s3 = do
  (s2,a3) <- asApp s3
  (s1,a2) <- asApp s2
  (s0,a1) <- asApp s1
  when (s0 /= op) $ fail "Unexpected op"
  return (a1,a2,a3)

-- | Returns term as an integer if it is an integer, signed
-- bitvector, or unsigned bitvector.
scViewAsNum :: SharedTerm s -> Maybe Integer
scViewAsNum (asNatLit -> Just i) = Just i
scViewAsNum _ = Nothing
-- FIXME: add patterns for bitvector constructors.

-- | Returns term as a constant Boolean if it can be evaluated as one.
-- bh: Is this really intended to do *evaluation*? Or is it supposed to work like asNatLit?
scViewAsBool :: SharedTerm s -> Maybe Bool
scViewAsBool = undefined --FIXME