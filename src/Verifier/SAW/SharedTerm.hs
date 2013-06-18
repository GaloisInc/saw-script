{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE CPP #-}
module Verifier.SAW.SharedTerm
  ( TermF(..)
  , Ident, mkIdent
  , VarIndex
  , ExtCns(..)
    -- * Shared terms
  , SharedTerm(..)
  , TermIndex
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
  , scFreshGlobalVar
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
  , scString
  , scNat
  , scNatType
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
  , scTermCount
  , scPrettyTerm
  , scPrettyTermDoc
  , scGlobalApply
  , scSharedTerm
    -- ** Type checking
  , scTypeOf
  , scTypeOfGlobal
    -- ** Prelude operations
  , scAppend
  , scGet
  , scIte
  , scSingle
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
  , scInstantiateExt
  ) where

import Control.Applicative
-- ((<$>), pure, (<*>))
import Control.Concurrent.MVar
import Control.Lens
import Control.Monad.Ref
import Control.Monad.State.Strict as State
import Data.Foldable hiding (sum)
import Data.Hashable (Hashable(..))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap
import Data.IORef (IORef)

import Data.Map (Map)
import qualified Data.Map as Map
#if __GLASGOW_HASKELL__ < 706
import qualified Data.Map as StrictMap
#else
import qualified Data.Map.Strict as StrictMap
#endif
import Data.Traversable ()
import qualified Data.Vector as V
import Data.Word
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.Leijen hiding ((<$>))

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.Recognizer
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

instance Termlike (SharedTerm s) where
  unwrapTermF (STApp _ tf) = tf

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
  show FTermF{} = "termF fTermF"
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

reducePi :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
reducePi sc (STApp _ (Pi _ _ body)) arg = instantiateVar sc 0 arg body
reducePi _ _ _ = error "reducePi: not a Pi term"

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

-- TODO: separate versions of typeOf: One fast one that assumes the
-- term is well-formed. Another that completely typechecks a term,
-- ensuring that it is well-formed. The full typechecking should use
-- memoization on subterms. Perhaps the fast one won't need to?

scTypeOf :: forall s. SharedContext s -> SharedTerm s -> IO (SharedTerm s)
scTypeOf sc t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: SharedTerm s -> State.StateT (Map TermIndex (SharedTerm s)) IO (SharedTerm s)
    memo (STApp i t) = do
      table <- State.get
      case Map.lookup i table of
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
        Lambda _ _ _ -> error "scTypeOf Lambda"
        Pi _ tp rhs -> do
          ltp <- sort tp
          rtp <- sort rhs
          lift $ scSort sc (max ltp rtp)
        Let defs rhs -> error "scTypeOf Let" defs rhs
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
        NatLit _ -> lift $ scNatType sc
        ArrayValue tp vs -> lift $ do
          n <- scNat sc (fromIntegral (V.length vs))
          scFlatTermF sc (DataTypeApp preludeVecIdent [n, tp])
        FloatLit{}  -> lift $ scFlatTermF sc (DataTypeApp preludeFloatIdent  [])
        DoubleLit{} -> lift $ scFlatTermF sc (DataTypeApp preludeDoubleIdent [])
        StringLit{} -> lift $ scFlatTermF sc (DataTypeApp preludeStringIdent [])
        ExtCns ec   -> return $ ecType ec

-- | The inverse function to @sharedTerm@.
unshare :: forall s. SharedTerm s -> Term
unshare t0 = State.evalState (go t0) Map.empty
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

{-
sharedTerm :: AppCacheRef s -> Term -> IO (SharedTerm s)
sharedTerm ref = go
    where go (Term termf) = getTerm ref =<< traverse go termf
-}

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
instantiateVars sc f initialLevel t0 =
    do cache <- newCache
       let ?cache = cache in go initialLevel t0
  where
    go :: (?cache :: Cache IORef (TermIndex, DeBruijnIndex) (Change (SharedTerm s))) =>
          DeBruijnIndex -> SharedTerm s -> ChangeT IO (SharedTerm s)
    go l t@(STApp tidx tf) =
        ChangeT $ useCache ?cache (tidx, l) (runChangeT $ preserveChangeT t (go' l tf))

    go' :: (?cache :: Cache IORef (TermIndex, DeBruijnIndex) (Change (SharedTerm s))) =>
           DeBruijnIndex -> TermF (SharedTerm s) -> ChangeT IO (IO (SharedTerm s))
    go' l (FTermF tf) = scFlatTermF sc <$> (traverse (go l) tf)
    go' l (Lambda i tp rhs) = scTermF sc <$> (Lambda i <$> go l tp <*> go (l+1) rhs)
    go' l (Pi i lhs rhs)    = scTermF sc <$> (Pi i <$> go l lhs <*> go (l+1) rhs)
    go' l (Let defs r) = scTermF sc <$> (Let <$> changeList procDef defs <*> go l' r)
      where l' = l + length defs
            procDef :: LocalDef (SharedTerm s) -> ChangeT IO (LocalDef (SharedTerm s))
            procDef (Def sym tp eqs) = Def sym <$> go l tp <*> changeList procEq eqs
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
    | j == 0    = return
    | otherwise = instantiateVars sc fn initialLevel
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
        term :: (?cache :: Cache IORef DeBruijnIndex (SharedTerm s)) =>
                DeBruijnIndex -> ChangeT IO (SharedTerm s)
        term i = useCache ?cache i (incVarsChangeT sc 0 i t0)
        -- Instantiate variable 0.
        fn :: (?cache :: Cache IORef DeBruijnIndex (SharedTerm s)) =>
              DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
                            -> ChangeT IO (IO (SharedTerm s))
        fn i j x | j  > i + k = taint $ scTermF sc <$> (LocalVar (j - 1) <$> x)
                 | j == i + k = taint $ return <$> term i
                 | otherwise  = scTermF sc <$> (LocalVar j <$> x)

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
       -> DeBruijnIndex -> DeBruijnIndex -> ChangeT IO (SharedTerm s)
       -> ChangeT IO (IO (SharedTerm s))
    fn rs i j x | j >= i + k + l = taint $ scTermF sc <$> (LocalVar (j - l) <$> x)
                | j >= i + k     = taint $ return <$> term (rs !! (j - i - k)) i
                | otherwise      = scTermF sc <$> (LocalVar j <$> x)

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

scString :: SharedContext s -> String -> IO (SharedTerm s)
scString sc s = scFlatTermF sc (StringLit s)

scVector :: SharedContext s -> SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scVector sc e xs = scFlatTermF sc (ArrayValue e (V.fromList xs))

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
              put $ StrictMap.insert t 1 m
              let (h,args) = asApplyAll t
              rec (Data.Foldable.foldr' (:) (args++r) (unwrapTermF h))
--              rec (Data.Foldable.foldr' (:) r (unwrapTermF t))

lineSep :: [Doc] -> Doc
lineSep l = hcat (punctuate line l)

scPrettyTermDoc :: forall s . SharedTerm s -> Doc
scPrettyTermDoc t0
    | null bound = ppt lcls0 PrecNone t0
    | otherwise =
        text "let { " <> nest 6 (lineSep lets) <$$>
        text "    }" <$$>
        text " in " <> ppt lcls0 PrecLetTerm t0
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
scLambda sc varname ty body = scTermF sc (Lambda (PVar varname 0 ty) ty body)

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
           -> SharedTerm s
           -> IO (SharedTerm s)
scLocalVar sc i t = scTermF sc (LocalVar i t)

scGlobalApply :: SharedContext s -> Ident -> [SharedTerm s] -> IO (SharedTerm s)
scGlobalApply sc i ts =
    do c <- scGlobalDef sc i
       scApplyAll sc c ts

------------------------------------------------------------
-- Building terms using prelude functions

scBoolType :: SharedContext s -> IO (SharedTerm s)
scBoolType sc = scFlatTermF sc (DataTypeApp "Prelude.Bool" [])

scNatType :: SharedContext s -> IO (SharedTerm s)
scNatType sc = scFlatTermF sc (DataTypeApp preludeNatIdent [])

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

-- | get :: (n :: Nat) -> (e :: sort 1) -> Vec n e -> Fin n -> e;
scGet :: SharedContext s -> SharedTerm s -> SharedTerm s ->
         SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scGet sc n e v i = scGlobalApply sc (mkIdent preludeName "get") [n, e, v, i]

-- | single :: (e :: sort 1) -> e -> Vec 1 e;
-- single e x = generate 1 e (\(i :: Fin 1) -> x);
scSingle :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scSingle sc e x = scGlobalApply sc (mkIdent preludeName "single") [e, x]

-- Primitive operations on bitvectors

-- | bitvector :: (n : Nat) -> sort 1
-- bitvector n = Vec n Bool
scBitvector :: SharedContext s -> Integer -> IO (SharedTerm s)
scBitvector sc size = do
  c <- scGlobalDef sc "Prelude.bitvector"
  s <- scNat sc size
  scApply sc c s

-- | bvNat :: (x :: Nat) -> Nat -> bitvector x;
scBvNat :: SharedContext s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvNat sc x y = scGlobalApply sc "Prelude.bvNat" [x, y]

-- | bvAdd/Sub/Mul :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
scBvAdd, scBvSub, scBvMul
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvAdd sc n x y = scGlobalApply sc "Prelude.bvAdd" [n, x, y]
scBvSub sc n x y = scGlobalApply sc "Prelude.bvSub" [n, x, y]
scBvMul sc n x y = scGlobalApply sc "Prelude.bvMul" [n, x, y]

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

-- | bvShl, bvShr :: (n :: Nat) -> bitvector n -> Nat -> bitvector n;
scBvShl, scBvShr
    :: SharedContext s -> SharedTerm s -> SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scBvShl sc n x y = scGlobalApply sc "Prelude.bvShl" [n, x, y]
scBvShr sc n x y = scGlobalApply sc "Prelude.bvShr" [n, x, y]

------------------------------------------------------------
-- | The default instance of the SharedContext operations.
mkSharedContext :: Module -> IO (SharedContext s)
mkSharedContext m = do
  vr <- newMVar 0 -- ^ Reference for getting variables.
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

-- | Instantiate some of the external constants
scInstantiateExt :: forall s 
                  . SharedContext s
                 -> Map VarIndex (SharedTerm s)
                 -> SharedTerm s
                 -> IO (SharedTerm s)
scInstantiateExt sc vmap t0 = do
  tcache <- newCacheMap' Map.empty
  let go :: SharedTerm s -> ChangeT IO (SharedTerm s) 
      go t@(STApp idx tf) =
        case tf of
          -- | Lookup variable in term if it is bound.
          FTermF (ExtCns ec) ->
            maybe (return t) modified $ Map.lookup (ecVarIndex ec) vmap
          -- | Recurse on other terms.
          _ -> useChangeCache tcache idx $
                 whenModified t (scTermF sc) (traverse go tf)
  commitChangeT (go t0)
