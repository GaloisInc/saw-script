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
    -- * Low-level AppCache interface for building shared terms
  , AppCacheRef
  , getTerm
    -- ** Utility functions using AppCache
  , instantiateVarList
    -- * High-level SharedContext interface for building shared terms
  , SharedContext
  , mkSharedContext
    -- ** Low-level generic term constructors
  , scTermF
  , scFlatTermF
    -- ** Implicit versions of functions.
  , scDefTerm
  , scFreshGlobal
  , scModule
  , scApply
  , scApplyAll
  , scMkRecord
  , scRecordSelect
  , scCtorApp
  , scApplyCtor
  , scFun
  , scNat
  , scBitvector
  , scFunAll
  , scLiteral
  , scLookupDef
  , scTuple
  , scTupleType
  , scTypeOf
  , scPrettyTerm
  , scViewAsBool
  , scViewAsNum
    -- ** Utilities
--  , scTrue
--  , scFalse
  ) where

import Control.Applicative ((<$>), pure, (<*>))
import Control.Concurrent.MVar
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
                     , acNextIdx :: !Word64
                     }

newtype AppCacheRef s = ACR (MVar (AppCache s))

emptyAppCache :: AppCache s
emptyAppCache = AC Map.empty 0

newAppCacheRef :: IO (AppCacheRef s)
newAppCacheRef = ACR <$> newMVar emptyAppCache

-- | Return term for application using existing term in cache if it is avaiable.
getTerm :: AppCacheRef s -> TermF (SharedTerm s) -> IO (SharedTerm s)
getTerm (ACR r) a =
  modifyMVar r $ \s -> do
    case Map.lookup a (acBindings s) of
      Just t -> return (s,t)
      Nothing -> seq s' $ return (s',t)
        where t = STApp (acNextIdx s) a
              s' = s { acBindings = Map.insert a t (acBindings s)
                     , acNextIdx = acNextIdx s + 1
                     }

getFlatTerm :: AppCacheRef s -> FlatTermF (SharedTerm s) -> IO (SharedTerm s)
getFlatTerm ac = getTerm ac . FTermF




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
subst0 = undefined

sortOfTerm :: SharedContext s -> SharedTerm s -> IO Sort
sortOfTerm sc t = do
  STApp _ (FTermF (Sort s)) <- scTypeOf sc t
  return s

typeOfGlobal :: SharedContext s -> Ident -> IO (SharedTerm s)
typeOfGlobal sc ident =
    do m <- scModule sc
       case findDef m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm sc (defType d)

typeOfFTermF :: SharedContext s
             -> FlatTermF (SharedTerm s)
             -> IO (SharedTerm s)
typeOfFTermF sc tf =
  case tf of
    GlobalDef d -> typeOfGlobal sc d
    App x y -> do
      STApp _ (Pi _ _ rhs) <- scTypeOf sc x
      subst0 sc rhs y
    TupleValue l -> scTupleType sc =<< mapM (scTypeOf sc) l
    TupleType l -> scSort sc . maximum =<< mapM (sortOfTerm sc) l
    RecordValue m -> scRecordType sc =<< mapM (scTypeOf sc) m
    RecordSelector t f -> do
      STApp _ (FTermF (RecordType m)) <- scTypeOf sc t
      let Just tp = Map.lookup f m
      return tp
    RecordType m -> scSort sc . maximum =<< mapM (sortOfTerm sc) m
    CtorApp c args -> undefined c args
    DataTypeApp dt args -> undefined dt args
    Sort s -> scSort sc (sortOf s)
    NatLit i -> undefined i
    ArrayValue tp _ -> undefined tp

scTypeOf :: SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scTypeOf sc (STVar _ _ tp) = return tp
scTypeOf sc (STApp _ tf) =
  case tf of
    FTermF ftf -> typeOfFTermF sc ftf
    Lambda (PVar i _ _) tp rhs -> do
      rtp <- scTypeOf sc rhs
      scTermF sc (Pi i tp rtp)
    Pi _ tp rhs -> do
      ltp <- sortOfTerm sc tp
      rtp <- sortOfTerm sc rhs
      scSort sc (max ltp rtp)
    Let defs rhs -> undefined defs rhs
    LocalVar _ tp -> return tp
--    EqType{} -> undefined 
--    Oracle{} -> undefined

{-
-- | Monadic fold with memoization
foldSharedTermM :: forall s b m . Monad m 
                => (VarIndex -> Ident -> SharedTerm s -> m b)
                -> (TermF b -> m b) -> SharedTerm s -> m b
foldSharedTermM g f = \t -> State.evalStateT (go t) Map.empty
  where
    go :: SharedTerm s -> State.StateT (Map TermIndex b) m b
    go (STVar i sym tp) = lift $ g i sym tp
    go (STApp i t) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          t' <- Traversable.mapM go t
          x <- lift (f t')
          State.modify (Map.insert i x)
          return x
-}

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

sharedTerm :: AppCacheRef s -> Term -> IO (SharedTerm s)
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
  -- | Returns term as a constant Boolean if it can be evaluated as one.
  , scViewAsBool    :: SharedTerm s -> Maybe Bool
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

scLiteral :: SharedContext s -> Integer -> IO (SharedTerm s)
scLiteral sc n
  | 0 <= n = scFlatTermF sc (NatLit n)
  | otherwise = error $ "scLiteral: negative value " ++ show n

scMkRecord :: SharedContext s -> Map FieldName (SharedTerm s) -> IO (SharedTerm s)
scMkRecord sc m = scFlatTermF sc (RecordValue m)

scRecordSelect :: SharedContext s -> SharedTerm s -> FieldName -> IO (SharedTerm s)
scRecordSelect sc t fname = scFlatTermF sc (RecordSelector t fname)

scRecordType :: SharedContext s -> Map FieldName (SharedTerm s) -> IO (SharedTerm s)
scRecordType sc m = scFlatTermF sc (RecordType m)

scNat :: SharedContext s -> Integer -> IO (SharedTerm s)
scNat = error "scNat unimplemented"

scTuple :: SharedContext s -> [SharedTerm s] -> IO (SharedTerm s)
scTuple sc ts = scFlatTermF sc (TupleValue ts)

scTupleType :: SharedContext s -> [SharedTerm s] -> IO (SharedTerm s)
scTupleType sc ts = scFlatTermF sc (TupleType ts)

-- | Obtain term representation a bitvector with a given width and known
-- value.
scBitvector :: SharedContext s
            -> (SharedTerm s)
            -> Integer
            -> IO (SharedTerm s)
scBitvector = error "scBitvector unimplemented"

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

------------------------------------------------------------
-- | The default instance of the SharedContext operations.
mkSharedContext :: Module -> IO (SharedContext s)
mkSharedContext m = do
  vr <- newMVar  0 -- ^ Reference for getting variables.
  cr <- newAppCacheRef
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
           , scViewAsBool = undefined
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
