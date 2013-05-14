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
  , Termlike(..)
  , asTermF
  , asFTermF
  , asCtor
  , asDataType
  , asGlobalDef
  , isGlobalDef
  , asNatLit
  , asBool
    -- * Shared terms
  , SharedTerm(..)
  , TermIndex
  , looseVars
  , unshare
    -- * SharedContext interface for building shared terms
  , SC
  , SharedContext(scTermF')
  , mkSC
  , runSC
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
  , scInstantiateExt
  ) where

import Control.Applicative
-- ((<$>), pure, (<*>))
import Control.Lens
import Control.Monad.Reader
import Control.Monad.Ref
import Control.Monad.ST
import Control.Monad.State.Strict as State
import Data.Foldable hiding (sum)
import Data.Hashable (Hashable(..))
import Data.HashMap.Strict (HashMap)
import qualified Data.HashMap.Strict as HMap

import Data.Map (Map)
import qualified Data.Map as Map
#if __GLASGOW_HASKELL__ < 706
import qualified Data.Map as StrictMap
#else
import qualified Data.Map.Strict as StrictMap
#endif
import Data.STRef
import Data.Traversable ()
import qualified Data.Vector as V
import Data.Word
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.Leijen hiding ((<$>))

import Verifier.SAW.Cache
import Verifier.SAW.Change
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.TypedAST hiding (incVars, instantiateVarList)

class Termlike t where
  unwrapTermF :: t -> TermF t

asTermF :: Termlike t => t -> TermF t
asTermF = unwrapTermF

asFTermF :: Termlike t => t -> Maybe (FlatTermF t)
asFTermF (asTermF -> FTermF ftf) = Just ftf
asFTermF _ = Nothing

asCtor :: Termlike t => t -> Maybe (Ident, [t])
asCtor t = do CtorApp c l <- asFTermF t; return (c,l)

asDataType :: Termlike t => t -> Maybe (Ident, [t])
asDataType t = do DataTypeApp c l <- asFTermF t; return (c,l) 

asGlobalDef :: Termlike t => t -> Maybe Ident
asGlobalDef t = do GlobalDef i <- asFTermF t; return i

isGlobalDef :: Termlike t => Ident -> t -> Maybe ()
isGlobalDef i (asGlobalDef -> Just o) | i == o = Just ()
isGlobalDef _ _ = Nothing

asNatLit :: Termlike t => t -> Maybe Integer
asNatLit t = do NatLit i <- asFTermF t; return i

-- | Returns term as a constant Boolean if it can be evaluated as one.
-- bh: Is this really intended to do *evaluation*? Or is it supposed to work like asNatLit?
asBool :: Termlike t => t -> Maybe Bool
asBool (asCtor -> Just ("Prelude.True",  [])) = Just True
asBool (asCtor -> Just ("Prelude.False", [])) = Just False
asBool _ = Nothing

type TermIndex = Int -- Word64

data SharedTerm s
  = STApp !TermIndex !(TermF (SharedTerm s))

instance Hashable (SharedTerm s) where
    hashWithSalt x (STApp idx _) = hashWithSalt x idx

instance Eq (SharedTerm s) where
  STApp x _ == STApp y _ = x == y

instance Ord (SharedTerm s) where
  compare (STApp x _) (STApp y _) = compare x y

instance Termlike Term where
  unwrapTermF (Term tf) = tf

instance Termlike (SharedTerm s) where
  unwrapTermF (STApp _ tf) = tf

----------------------------------------------------------------------
-- SharedContext: a high-level interface for building SharedTerms.

data SharedContext s = SharedContext
  { -- | Returns the current module for the underlying global theory.
    scModule'        :: ST s Module
  , scTermF'         :: TermF (SharedTerm s) -> ST s (SharedTerm s)
  , scFreshGlobalVar' :: ST s VarIndex
  }

newtype SC s a = SC (ReaderT (SharedContext s) (ST s) a)
    deriving (Functor, Applicative, Monad)

instance MonadRef (STRef s) (SC s) where
    newRef    r   = SC $ lift $ newRef    r
    readRef   r   = SC $ lift $ readRef   r
    writeRef  r x = SC $ lift $ writeRef  r x
    modifyRef r f = SC $ lift $ modifyRef r f

mkSC :: (SharedContext s -> ST s a) -> SC s a
mkSC f = SC (ReaderT f)

runSC :: SC s a -> SharedContext s -> ST s a
runSC (SC r) = runReaderT r

scModule :: SC s Module
scModule = mkSC scModule'

scTermF :: TermF (SharedTerm s) -> SC s (SharedTerm s)
scTermF tf = mkSC (\sc -> scTermF' sc tf)

scFreshGlobalVar :: SC s VarIndex
scFreshGlobalVar = mkSC scFreshGlobalVar'

scFlatTermF :: FlatTermF (SharedTerm s) -> SC s (SharedTerm s)
scFlatTermF ftf = scTermF (FTermF ftf)

-- | Create a global variable with the given identifier (which may be "_") and type.
scFreshGlobal :: String -> SharedTerm s -> SC s (SharedTerm s)
scFreshGlobal sym tp = do
  i <- scFreshGlobalVar
  scFlatTermF (ExtCns (EC i sym tp))

-- | Returns shared term associated with ident.
-- Does not check module namespace.
scGlobalDef :: Ident -> SC s (SharedTerm s)
scGlobalDef ident = scFlatTermF (GlobalDef ident)

scApply :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scApply f = scFlatTermF . App f

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scDataTypeApp :: Ident -> [SharedTerm s] -> SC s (SharedTerm s)
scDataTypeApp ident args = scFlatTermF (DataTypeApp ident args)

-- | Applies the constructor with the given name to the list of
-- arguments. This version does no checking against the module.
scCtorApp :: Ident -> [SharedTerm s] -> SC s (SharedTerm s)
scCtorApp ident args = scFlatTermF (CtorApp ident args)

-- SharedContext implementation.

data AppCache s = AC { acBindings :: !(HashMap (TermF (SharedTerm s)) (SharedTerm s))
                     , acNextIdx :: !TermIndex
                     }

type AppCacheRef s = STRef s (AppCache s)

emptyAppCache :: AppCache s
emptyAppCache = AC HMap.empty 0

instance Show (TermF (SharedTerm s)) where
  show FTermF{} = "termF fTermF"
  show _ = "termF SharedTerm"

-- | Return term for application using existing term in cache if it is avaiable.
getTerm :: AppCacheRef s -> TermF (SharedTerm s) -> ST s (SharedTerm s)
getTerm r a = do
  s <- readSTRef r
  case HMap.lookup a (acBindings s) of
    Just t -> return t
    Nothing -> do
        writeSTRef r $! s'
        return t
      where t = STApp (acNextIdx s) a
            s' = s { acBindings = HMap.insert a t (acBindings s)
                   , acNextIdx = acNextIdx s + 1
                   }

reducePi :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
reducePi (STApp _ (Pi _ _ body)) arg = instantiateVar 0 arg body
reducePi _ _ = error "reducePi: not a Pi term"

scTypeOfGlobal :: Ident -> SC s (SharedTerm s)
scTypeOfGlobal ident =
    do m <- scModule
       case findDef m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm (defType d)

scTypeOfDataType :: Ident -> SC s (SharedTerm s)
scTypeOfDataType ident =
    do m <- scModule
       case findDataType m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm (dtType d)

scTypeOfCtor :: Ident -> SC s (SharedTerm s)
scTypeOfCtor ident =
    do m <- scModule
       case findCtor m ident of
         Nothing -> fail $ "Failed to find " ++ show ident ++ " in module."
         Just d -> scSharedTerm (ctorType d)

-- TODO: separate versions of typeOf: One fast one that assumes the
-- term is well-formed. Another that completely typechecks a term,
-- ensuring that it is well-formed. The full typechecking should use
-- memoization on subterms. Perhaps the fast one won't need to?

scTypeOf :: forall s. SharedTerm s -> SC s (SharedTerm s)
scTypeOf t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: SharedTerm s -> State.StateT (Map TermIndex (SharedTerm s)) (SC s) (SharedTerm s)
    memo (STApp i t) = do
      table <- State.get
      case Map.lookup i table of
        Just x  -> return x
        Nothing -> do
          x <- termf t
          State.modify (Map.insert i x)
          return x
    sort :: SharedTerm s -> State.StateT (Map TermIndex (SharedTerm s)) (SC s) Sort
    sort t = do
      STApp _ (FTermF (Sort s)) <- memo t
      return s
    termf :: TermF (SharedTerm s) -> State.StateT (Map TermIndex (SharedTerm s)) (SC s) (SharedTerm s)
    termf tf =
      case tf of
        FTermF ftf -> ftermf ftf
        Lambda (PVar i _ _) tp rhs -> do
          rtp <- memo rhs
          lift $ scTermF (Pi i tp rtp)
        Lambda _ _ _ -> error "scTypeOf Lambda"
        Pi _ tp rhs -> do
          ltp <- sort tp
          rtp <- sort rhs
          lift $ scSort (max ltp rtp)
        Let defs rhs -> undefined defs rhs
        LocalVar _ tp -> return tp
    ftermf :: FlatTermF (SharedTerm s)
           -> State.StateT (Map TermIndex (SharedTerm s)) (SC s) (SharedTerm s)
    ftermf tf =
      case tf of
        GlobalDef d -> lift $ scTypeOfGlobal d
        App x y -> do
          tx <- memo x
          lift $ reducePi tx y
        TupleValue l -> lift . scTupleType =<< traverse memo l
        TupleType l -> lift . scSort . maximum =<< traverse sort l
        TupleSelector t i -> do
          STApp _ (FTermF (TupleType ts)) <- memo t
          return (ts !! (i-1)) -- FIXME test for i < length ts
        RecordValue m -> lift . scRecordType =<< traverse memo m
        RecordSelector t f -> do
          STApp _ (FTermF (RecordType m)) <- memo t
          let Just tp = Map.lookup f m
          return tp
        RecordType m -> lift . scSort . maximum =<< traverse sort m
        CtorApp c args -> do
          t <- lift $ scTypeOfCtor c
          lift $ foldM reducePi t args
        DataTypeApp dt args -> do
          t <- lift $ scTypeOfDataType dt
          lift $ foldM reducePi t args
        Sort s -> lift $ scSort (sortOf s)
        NatLit _ -> lift $ scNatType
        ArrayValue tp _ -> error "typeOfFTermF ArrayValue" tp
        FloatLit{}  -> lift $ scFlatTermF (DataTypeApp preludeFloatIdent  [])
        DoubleLit{} -> lift $ scFlatTermF (DataTypeApp preludeDoubleIdent [])
        ExtCns{}    -> error "scTypeOf ExtCns"

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

sharedTerm :: STRef s (AppCache s) -> Term -> ST s (SharedTerm s)
sharedTerm ref = go
    where go (Term termf) = getTerm ref =<< traverse go termf

scSharedTerm :: Term -> SC s (SharedTerm s)
scSharedTerm = go
    where go (Term termf) = scTermF =<< traverse go termf

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

instantiateVars :: forall s.
                   (DeBruijnIndex -> DeBruijnIndex -> ChangeT (SC s) (SharedTerm s)
                                  -> ChangeT (SC s) (SC s (SharedTerm s)))
                -> DeBruijnIndex -> SharedTerm s -> ChangeT (SC s) (SharedTerm s)
instantiateVars f initialLevel t0 =
    do cache <- newCache
       let ?cache = cache in go initialLevel t0
  where
    go :: (?cache :: Cache (STRef s) (TermIndex, DeBruijnIndex) (Change (SharedTerm s))) =>
          DeBruijnIndex -> SharedTerm s -> ChangeT (SC s) (SharedTerm s)
    go l t@(STApp tidx tf) =
        ChangeT $ useCache ?cache (tidx, l) (runChangeT $ preserveChangeT t (go' l tf))

    go' :: (?cache :: Cache (STRef s) (TermIndex, DeBruijnIndex) (Change (SharedTerm s))) =>
           DeBruijnIndex -> TermF (SharedTerm s) -> ChangeT (SC s) (SC s (SharedTerm s))
    go' l (FTermF tf) = scFlatTermF <$> (traverse (go l) tf)
    go' l (Lambda i tp rhs) = scTermF <$> (Lambda i <$> go l tp <*> go (l+1) rhs)
    go' l (Pi i lhs rhs)    = scTermF <$> (Pi i <$> go l lhs <*> go (l+1) rhs)
    go' l (Let defs r) = scTermF <$> (Let <$> changeList procDef defs <*> go l' r)
      where l' = l + length defs
            procDef :: LocalDef (SharedTerm s) -> ChangeT (SC s) (LocalDef (SharedTerm s))
            procDef (LocalFnDef sym tp eqs) =
              LocalFnDef sym <$> go l tp <*> changeList procEq eqs
            procEq :: DefEqn (SharedTerm s) -> ChangeT (SC s) (DefEqn (SharedTerm s))
            procEq (DefEqn pats rhs) = DefEqn pats <$> go eql rhs
              where eql = l' + sum (patBoundVarCount <$> pats)
    go' l (LocalVar i tp)
      | i < l     = scTermF <$> (LocalVar i <$> go (l-(i+1)) tp)
      | otherwise = f l i (go (l-(i+1)) tp)

-- | @incVars j k t@ increments free variables at least @j@ by @k@.
-- e.g., incVars 1 2 (C ?0 ?1) = C ?0 ?3
incVarsChangeT :: DeBruijnIndex -> DeBruijnIndex -> SharedTerm s -> ChangeT (SC s) (SharedTerm s)
incVarsChangeT initialLevel j
    | j == 0    = return
    | otherwise = instantiateVars fn initialLevel
    where
      fn _ i t = taint $ scTermF <$> (LocalVar (i+j) <$> t)

incVars :: DeBruijnIndex -> DeBruijnIndex -> SharedTerm s -> SC s (SharedTerm s)
incVars i j t = commitChangeT (incVarsChangeT i j t)

-- | Substitute @t0@ for variable @k@ in @t@ and decrement all higher
-- dangling variables.
instantiateVarChangeT :: forall s. DeBruijnIndex -> SharedTerm s -> SharedTerm s
                      -> ChangeT (SC s) (SharedTerm s)
instantiateVarChangeT k t0 t =
    do cache <- newCache
       let ?cache = cache in instantiateVars fn 0 t
  where -- Use map reference to memoize instantiated versions of t.
        term :: (?cache :: Cache (STRef s) DeBruijnIndex (SharedTerm s)) =>
                DeBruijnIndex -> ChangeT (SC s) (SharedTerm s)
        term i = useCache ?cache i (incVarsChangeT 0 i t0)
        -- Instantiate variable 0.
        fn :: (?cache :: Cache (STRef s) DeBruijnIndex (SharedTerm s)) =>
              DeBruijnIndex -> DeBruijnIndex -> ChangeT (SC s) (SharedTerm s)
                            -> ChangeT (SC s) (SC s (SharedTerm s))
        fn i j x | j  > i + k = taint $ scTermF <$> (LocalVar (j - 1) <$> x)
                 | j == i + k = taint $ return <$> term i
                 | otherwise  = scTermF <$> (LocalVar j <$> x)

-- | Substitute @t0@ for variable @k@ in @t@ and decrement all higher
-- dangling variables.
instantiateVar :: DeBruijnIndex -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
instantiateVar k t0 t = commitChangeT (instantiateVarChangeT k t0 t)

-- | Substitute @ts@ for variables @[k .. k + length ts - 1]@ and
-- decrement all higher loose variables by @length ts@.
instantiateVarListChangeT :: forall s. DeBruijnIndex -> [SharedTerm s]
                          -> SharedTerm s -> ChangeT (SC s) (SharedTerm s)
instantiateVarListChangeT _ [] t = return t
instantiateVarListChangeT k ts t =
    do caches <- mapM (const newCache) ts
       instantiateVars (fn (zip caches ts)) 0 t
  where
    l = length ts
    -- Memoize instantiated versions of ts.
    term :: (Cache (STRef s) DeBruijnIndex (SharedTerm s), SharedTerm s)
         -> DeBruijnIndex -> ChangeT (SC s) (SharedTerm s)
    term (cache, x) i = useCache cache i (incVarsChangeT 0 i x)
    -- Instantiate variables [k .. k+l-1].
    fn :: [(Cache (STRef s) DeBruijnIndex (SharedTerm s), SharedTerm s)]
       -> DeBruijnIndex -> DeBruijnIndex -> ChangeT (SC s) (SharedTerm s)
       -> ChangeT (SC s) (SC s (SharedTerm s))
    fn rs i j x | j >= i + k + l = taint $ scTermF <$> (LocalVar (j - l) <$> x)
                | j >= i + k     = taint $ return <$> term (rs !! (j - i - k)) i
                | otherwise      = scTermF <$> (LocalVar j <$> x)

instantiateVarList :: DeBruijnIndex -> [SharedTerm s] -> SharedTerm s -> SC s (SharedTerm s)
instantiateVarList k ts t = commitChangeT (instantiateVarListChangeT k ts t)

scApplyAll :: SharedTerm s -> [SharedTerm s] -> SC s (SharedTerm s)
scApplyAll = foldlM scApply

-- | Returns the defined constant with the given name. Fails if no
-- such constant exists in the module.
scLookupDef :: Ident -> SC s (SharedTerm s)
scLookupDef ident = scGlobalDef ident --FIXME: implement module check.

-- | Deprecated. Use scGlobalDef or scLookupDef instead.
scDefTerm :: TypedDef -> SC s (SharedTerm s)
scDefTerm d = scGlobalDef (defIdent d)

-- TODO: implement version of scCtorApp that looks up the arity of the
-- constructor identifier in the module.

-- | Deprecated. Use scCtorApp instead.
scApplyCtor :: TypedCtor -> [SharedTerm s] -> SC s (SharedTerm s)
scApplyCtor c args = scCtorApp (ctorName c) args

scSort :: Sort -> SC s (SharedTerm s)
scSort s = scFlatTermF (Sort s)

scNat :: Integer -> SC s (SharedTerm s)
scNat n
  | 0 <= n = scFlatTermF (NatLit n)
  | otherwise = error $ "scNat: negative value " ++ show n

scMkRecord :: Map FieldName (SharedTerm s) -> SC s (SharedTerm s)
scMkRecord m = scFlatTermF (RecordValue m)

scRecordSelect :: SharedTerm s -> FieldName -> SC s (SharedTerm s)
scRecordSelect t fname = scFlatTermF (RecordSelector t fname)

scRecordType :: Map FieldName (SharedTerm s) -> SC s (SharedTerm s)
scRecordType m = scFlatTermF (RecordType m)

scTuple :: [SharedTerm s] -> SC s (SharedTerm s)
scTuple ts = scFlatTermF (TupleValue ts)

scTupleType :: [SharedTerm s] -> SC s (SharedTerm s)
scTupleType ts = scFlatTermF (TupleType ts)

scTupleSelector :: SharedTerm s -> Int -> SC s (SharedTerm s)
scTupleSelector t i = scFlatTermF (TupleSelector t i)

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
              let (h,args) = asAppList t
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

scFun :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scFun a b = do b' <- incVars 0 1 b
               scTermF (Pi "_" a b')

scFunAll :: [SharedTerm s] -> SharedTerm s -> SC s (SharedTerm s)
scFunAll argTypes resultType = foldrM scFun resultType argTypes

scLambda :: String -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scLambda varname ty body = scTermF (Lambda (PVar varname 0 ty) ty body)

scLocalVar :: DeBruijnIndex -> SharedTerm s -> SC s (SharedTerm s)
scLocalVar i t = scTermF (LocalVar i t)

scGlobalApply :: Ident -> [SharedTerm s] -> SC s (SharedTerm s)
scGlobalApply i ts =
    do c <- scGlobalDef i
       scApplyAll c ts

------------------------------------------------------------
-- Building terms using prelude functions

scBoolType :: SC s (SharedTerm s)
scBoolType = scFlatTermF (DataTypeApp "Prelude.Bool" [])

scNatType :: SC s (SharedTerm s)
scNatType = scFlatTermF (DataTypeApp preludeNatIdent [])

-- ite :: (a :: sort 1) -> Bool -> a -> a -> a;
scIte :: SharedTerm s -> SharedTerm s ->
         SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scIte t b x y = scGlobalApply "Prelude.ite" [t, b, x, y]

-- append :: (m n :: Nat) -> (e :: sort 0) -> Vec m e -> Vec n e -> Vec (addNat m n) e;
scAppend :: SharedTerm s -> SharedTerm s -> SharedTerm s ->
            SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scAppend t m n x y = scGlobalApply "Prelude.append" [m, n, t, x, y]

-- | slice :: (e :: sort 1) -> (i n o :: Nat) -> Vec (addNat (addNat i n) o) e -> Vec n e;
scSlice :: SharedTerm s -> SharedTerm s ->
           SharedTerm s -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scSlice e i n o a = scGlobalApply "Prelude.slice" [e, i, n, o, a]

-- Primitive operations on bitvectors

-- | bitvector :: (n : Nat) -> sort 1
-- bitvector n = Vec n Bool
scBitvector :: Integer -> SC s (SharedTerm s)
scBitvector size = do
  c <- scGlobalDef "Prelude.bitvector"
  s <- scNat size
  scApply c s

-- | bvNat :: (x :: Nat) -> Nat -> bitvector x;
scBvNat :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scBvNat x y = scGlobalApply "Prelude.bvNat" [x, y]

-- | bvAdd/Sub/Mul :: (x :: Nat) -> bitvector x -> bitvector x -> bitvector x;
scBvAdd, scBvSub, scBvMul
    :: SharedTerm s -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scBvAdd n x y = scGlobalApply "Prelude.bvAdd" [n, x, y]
scBvSub n x y = scGlobalApply "Prelude.bvSub" [n, x, y]
scBvMul n x y = scGlobalApply "Prelude.bvMul" [n, x, y]

-- | bvOr/And/Xor :: (n :: Nat) -> bitvector n -> bitvector n -> bitvector n;
scBvOr, scBvAnd, scBvXor
    :: SharedTerm s -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scBvAnd n x y = scGlobalApply "Prelude.bvAnd" [n, x, y]
scBvXor n x y = scGlobalApply "Prelude.bvXor" [n, x, y]
scBvOr  n x y = scGlobalApply "Prelude.bvOr"  [n, x, y]

-- | bvNot :: (n :: Nat) -> bitvector n -> bitvector n;
scBvNot :: SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scBvNot n x = scGlobalApply "Prelude.bvNot" [n, x]

-- | bvEq :: (n :: Nat) -> bitvector n -> bitvector n -> Bool;
scBvEq, scBvUGe, scBvUGt, scBvULe, scBvULt
    :: SharedTerm s -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scBvEq  n x y = scGlobalApply "Prelude.bvEq"  [n, x, y]
scBvUGe n x y = scGlobalApply "Prelude.bvuge" [n, x, y]
scBvULe n x y = scGlobalApply "Prelude.bvule" [n, x, y]
scBvUGt n x y = scGlobalApply "Prelude.bvugt" [n, x, y]
scBvULt n x y = scGlobalApply "Prelude.bvult" [n, x, y]

-- | bvShl, bvShr :: (n :: Nat) -> bitvector n -> Nat -> bitvector n;
scBvShl, scBvShr
    :: SharedTerm s -> SharedTerm s -> SharedTerm s -> SC s (SharedTerm s)
scBvShl n x y = scGlobalApply "Prelude.bvShl" [n, x, y]
scBvShr n x y = scGlobalApply "Prelude.bvShr" [n, x, y]

------------------------------------------------------------
-- | The default instance of the SharedContext operations.
mkSharedContext :: Module -> ST s (SharedContext s)
mkSharedContext m = do
  vr <- newSTRef 0 -- ^ Reference for getting variables.
  cr <- newSTRef emptyAppCache
  let freshGlobalVar = do i <- readSTRef vr
                          writeSTRef vr (i+1)
                          return i
  return SharedContext {
             scModule' = return m
           , scTermF' = getTerm cr
           , scFreshGlobalVar' = freshGlobalVar
           }

asApp :: SharedTerm s -> Maybe (SharedTerm s, SharedTerm s)
asApp t = do App x y <- asFTermF t; return (x,y)

asAppList :: SharedTerm s -> (SharedTerm s, [SharedTerm s])
asAppList = go []
  where go l t =
          case asApp t of
            Just (f,v) -> go (v:l) f
            Nothing -> (t,l)

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
                  . Map VarIndex (SharedTerm s)
                 -> SharedTerm s
                 -> SC s (SharedTerm s)
scInstantiateExt vmap t0 = do
  tcache <- newCacheMap' Map.empty
  let go :: SharedTerm s -> ChangeT (SC s) (SharedTerm s) 
      go t@(STApp idx tf) =
        case tf of
          -- | Lookup variable in term if it is bound.
          FTermF (ExtCns ec) ->
            maybe (return t) modified $ Map.lookup (ecVarIndex ec) vmap
          -- | Recurse on other terms.
          _ -> useChangeCache tcache idx $
                 whenModified t scTermF (traverse go tf)
  commitChangeT (go t0)
