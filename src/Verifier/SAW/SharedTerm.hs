{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.SharedTerm
  ( TermF(..)
  , Ident, mkIdent
  , SharedTerm(..)
  , TermIndex
  , unwrapSharedTerm
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
  , scTypeOf
  , scPrettyTerm
  , scViewAsBool
  , scViewAsNum
  , scGlobalApply
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
  , instantiateVarList
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Concurrent.MVar
import Control.Monad (foldM)
import qualified Control.Monad.State as State
import Control.Monad.Trans (lift)
import Data.IORef
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Word
import Data.Foldable hiding (sum)
import Data.Traversable
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.HughesPJ

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.TypedAST hiding (incVars, instantiateVarList)

type TermIndex = Word64
type VarIndex = Word64

data SharedTerm s
  = STVar !VarIndex !Ident !(SharedTerm s)
  | STApp !TermIndex !(TermF (SharedTerm s))

instance Eq (SharedTerm s) where
  STVar x _ _ == STVar y _ _ = x == y
  STApp x _ == STApp y _ = x == y
  _ == _ = False

instance Ord (SharedTerm s) where
  compare (STVar x _ _) (STVar y _ _) = compare x y
  compare STVar{} _ = LT
  compare _ STVar{} = GT
  compare (STApp x _) (STApp y _) = compare x y

unwrapSharedTerm :: SharedTerm s -> TermF (SharedTerm s)
unwrapSharedTerm (STApp _ tf) = tf

data AppCache s = AC { acBindings :: !(Map (TermF (SharedTerm s)) (SharedTerm s))
                     , acNextIdx :: !TermIndex
                     }

emptyAppCache :: AppCache s
emptyAppCache = AC Map.empty 0

-- | Return term for application using existing term in cache if it is avaiable.
getTerm :: MVar (AppCache s) -> TermF (SharedTerm s) -> IO (SharedTerm s)
getTerm r a =
  modifyMVar r $ \s -> do
    case Map.lookup a (acBindings s) of
      Just t -> return (s,t)
      Nothing -> seq s' $ return (s',t)
        where t = STApp (acNextIdx s) a
              s' = s { acBindings = Map.insert a t (acBindings s)
                     , acNextIdx = acNextIdx s + 1
                     }

{-
data LocalVarTypeMap s = LVTM { lvtmMap :: Map Integer (SharedTerm s) }

consLocalVarType :: LocalVarTypeMap s -> Ident -> SharedTerm s -> LocalVarTypeMap s
consLocalVarType = undefined

localVarType :: DeBruijnIndex -> LocalVarTypeMap s -> SharedTerm s
localVarType = undefined
-}

-- | Substitute var 0 in first term for second term, and shift all variable
-- references down.
subst0 :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
subst0 sc t t0 = instantiateVar sc 0 t0 t

reducePi :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
reducePi sc (STApp _ (Pi _ _ body)) arg = instantiateVar sc 0 arg body
reducePi _ _ _ = error "reducePi: not a Pi term"

typeOfGlobal :: SharedContext s -> Ident -> IO (SharedTerm s)
typeOfGlobal sc ident =
    do m <- scModule sc
       case findDef m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm sc (defType d)

typeOfDataType :: SharedContext s -> Ident -> IO (SharedTerm s)
typeOfDataType sc ident =
    do m <- scModule sc
       case findDataType m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm sc (dtType d)

typeOfCtor :: SharedContext s -> Ident -> IO (SharedTerm s)
typeOfCtor sc ident =
    do m <- scModule sc
       case findCtor m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm sc (ctorType d)

-- TODO: separate versions of typeOf: One fast one that assumes the
-- term is well-formed. Another that completely typechecks a term,
-- ensuring that it is well-formed. The full typechecking should use
-- memoization on subterms. Perhaps the fast one won't need to?

scTypeOf :: forall s. SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scTypeOf sc t = State.evalStateT (memo t) Map.empty
  where
    memo :: SharedTerm s -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    memo (STVar i sym tp) = return tp
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
    ftermf :: FlatTermF (SharedTerm s) -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    ftermf tf =
      case tf of
        GlobalDef d -> lift $ typeOfGlobal sc d
        App x y -> do
          tx <- memo x
          lift $ reducePi sc tx y
        TupleValue l -> lift . scTupleType sc =<< mapM memo l
        TupleType l -> lift . scSort sc . maximum =<< mapM sort l
        TupleSelector t i -> do
          STApp _ (FTermF (TupleType ts)) <- memo t
          return (ts !! (i-1)) -- FIXME test for i < length ts
        RecordValue m -> lift . scRecordType sc =<< mapM memo m
        RecordSelector t f -> do
          STApp _ (FTermF (RecordType m)) <- memo t
          let Just tp = Map.lookup f m
          return tp
        RecordType m -> lift . scSort sc . maximum =<< mapM sort m
        CtorApp c args -> do
          t <- lift $ typeOfCtor sc c
          lift $ foldM (reducePi sc) t args
        DataTypeApp dt args -> do
          t <- lift $ typeOfDataType sc dt
          lift $ foldM (reducePi sc) t args
        Sort s -> lift $ scSort sc (sortOf s)
        NatLit i -> lift $ scNatType sc
        ArrayValue tp _ -> error "typeOfFTermF ArrayValue" tp

-- | The inverse function to @sharedTerm@.
unshare :: forall s. SharedTerm s -> Term
unshare t = State.evalState (go t) Map.empty
  where
    go :: SharedTerm s -> State.State (Map TermIndex Term) Term
    go (STVar i sym tp) = error "unshare STVar"
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

instantiateVars :: forall s. SharedContext s
                -> (DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
                                  -> ChangeT IO (IO (SharedTerm s)))
                -> DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
instantiateVars sc f initialLevel t =
    do cache <- newCache
       let ?cache = cache in go initialLevel t
  where
    go :: (?cache :: Cache (ChangeT IO) (TermIndex, DeBruijnIndex) (SharedTerm s)) =>
          DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
    go l t@(STVar {}) = pure t
    go l t@(STApp tidx tf) =
        useCache ?cache (tidx, l) (preserveChangeT t $ go' l tf)

    go' :: (?cache :: Cache (ChangeT IO) (TermIndex, DeBruijnIndex) (SharedTerm s)) =>
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
--    go' l (EqType lhs rhs) = scTermF sc <$> (EqType <$> go l lhs <*> go l rhs)
--    go' l (Oracle s prop) = scTermF sc <$> (Oracle s <$> go l prop)

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

----------------------------------------------------------------------
-- SharedContext: a high-level interface for building SharedTerms.

-- | Operations that are defined, but not 
data SharedContext s = SharedContext
  { -- | Returns the current module for the underlying global theory.
    scModule :: IO Module
  , scTermF         :: TermF (SharedTerm s) -> IO (SharedTerm s)
  -- | Create a global variable with the given identifier (which may be "_") and type.
  , scFreshGlobal   :: Ident -> SharedTerm s -> IO (SharedTerm s)
  }

scFlatTermF :: SharedContext s -> FlatTermF (SharedTerm s) -> IO (SharedTerm s)
scFlatTermF sc ftf = scTermF sc (FTermF ftf)

scApply :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scApply sc f x = scFlatTermF sc (App f x)

scApplyAll :: SharedContext s -> SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scApplyAll sc = foldlM (scApply sc)

-- | This version does no checking against the module namespace.
scGlobalDef :: SharedContext s -> Ident -> IO (SharedTerm s)
scGlobalDef sc ident = scFlatTermF sc (GlobalDef ident)

-- | Returns the defined constant with the given name. Fails if no
-- such constant exists in the module.
scLookupDef :: SharedContext s -> Ident -> IO (SharedTerm s)
scLookupDef sc ident = scGlobalDef sc ident --FIXME: implement module check.

-- | Deprecated. Use scGlobalDef or scLookupDef instead.
scDefTerm :: SharedContext s -> TypedDef -> IO (SharedTerm s)
scDefTerm sc d = scGlobalDef sc (defIdent d)

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scCtorApp :: SharedContext s -> Ident -> [SharedTerm s] -> IO (SharedTerm s)
scCtorApp sc ident args = scFlatTermF sc (CtorApp ident args)

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

-- TODO: remove unused SharedContext argument
scPrettyTermDoc :: SharedContext s -> SharedTerm s -> Doc
scPrettyTermDoc _sc t = ppTerm emptyLocalVarDoc 0 (unshare t)

scPrettyTerm :: SharedContext s -> SharedTerm s -> String
scPrettyTerm sc t = show (scPrettyTermDoc sc t)

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

preludeName :: ModuleName
preludeName = mkModuleName ["Prelude"]

scBoolType :: SharedContext s -> IO (SharedTerm s)
scBoolType sc = scFlatTermF sc (DataTypeApp (mkIdent preludeName "Bool") [])

scNatType :: SharedContext s -> IO (SharedTerm s)
scNatType sc = scFlatTermF sc (DataTypeApp (mkIdent preludeName "Nat") [])

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
        i <- modifyMVar vr (\i -> return (i,i+1))
        return (STVar i sym tp)
  return SharedContext {
             scModule = return m
           , scTermF = getTerm cr
           , scFreshGlobal = freshGlobal
           }

asNatLit :: SharedTerm s -> Maybe Integer
asNatLit (STApp _ (FTermF (NatLit i))) = Just i
asNatLit _ = Nothing

asApp :: SharedTerm s -> Maybe (SharedTerm s, SharedTerm s)
asApp (STApp _ (FTermF (App t u))) = Just (t,u)
asApp _ = Nothing

asApp3Of :: SharedTerm s -> SharedTerm s -> Maybe (SharedTerm s, SharedTerm s, SharedTerm s)
asApp3Of op s3 = do
  (s2,a3) <- asApp s3
  (s1,a2) <- asApp s2
  (s0,a1) <- asApp s1
  if s0 == op then return (a1,a2,a3) else fail ""

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
