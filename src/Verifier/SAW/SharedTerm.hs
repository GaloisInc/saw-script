{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

module Verifier.SAW.SharedTerm
  ( ParamType(..)
  , TermF(..)
  , Ident, mkIdent
  , SharedTerm
  , SharedContext(..)
  , mkSharedContext
    -- ** Implicit versions of functions.
  , scApply
  , scApplyAll
  , scFreshGlobal
  , scRecordSelect
  , scTrue
  , scFalse
  , scInteger
  , scTypeOf
  , scPrettyTerm
    -- ** Utilities
  , scViewAsBool
  , scViewAsNum
  ) where

import Control.Applicative ((<$>))
import Control.Monad ()
import Control.Concurrent.MVar
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Word
import Data.Foldable
import Data.Traversable
import Prelude hiding (mapM, maximum)
import Text.PrettyPrint.HughesPJ
import qualified Control.Monad.State as State
import Control.Monad.Trans (lift)
import qualified Data.Traversable as Traversable

import Verifier.SAW.TypedAST

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

-- | Operations that are defined, but not 
data SharedContext s = SharedContext
  { -- | Returns the current module for the underlying global theory.
    scCurrentModuleFn :: IO Module
  , scTrueTerm        :: SharedTerm s
  , scFalseTerm       :: SharedTerm s
     -- Returns the globals in the current scope as a record of functions.
  , scFreshGlobalFn   :: Ident -> SharedTerm s -> IO (SharedTerm s)
     -- | @scApplyFn f x@ returns the result of applying @x@ to a lambda function @x@.
  , scApplyFn         :: SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
  , scMkRecordFn      :: Map String (SharedTerm s) -> IO (SharedTerm s)
    -- | Select an element out of a record.
  , scRecordSelectFn  :: SharedTerm s -> FieldName -> IO (SharedTerm s)
  , scIntegerFn       :: Integer -> IO (SharedTerm s)
  , scTypeOfFn        :: SharedTerm s -> IO (SharedTerm s)
  , scPrettyTermDocFn :: SharedTerm s -> Doc
  , scViewAsNumFn     :: SharedTerm s -> Maybe Integer
  }

scApply :: (?sc :: SharedContext s) => SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
scApply = scApplyFn ?sc

scApplyAll :: (?sc :: SharedContext s) => SharedTerm s -> [SharedTerm s] -> IO (SharedTerm s)
scApplyAll = foldlM scApply

scRecordSelect :: (?sc :: SharedContext s) => SharedTerm s -> FieldName -> IO (SharedTerm s)
scRecordSelect = scRecordSelectFn ?sc

scInteger :: (?sc :: SharedContext s) => Integer -> IO (SharedTerm s)
scInteger = scIntegerFn ?sc

scTypeOf :: (?sc :: SharedContext s) => SharedTerm s -> IO (SharedTerm s)
scTypeOf = scTypeOfFn ?sc

-- | Create a global variable with the given identifier (which may be "_") and type.
scFreshGlobal :: (?sc :: SharedContext s)
              => Ident -> SharedTerm s 
              -> IO (SharedTerm s)
scFreshGlobal = scFreshGlobalFn ?sc

scTrue :: (?sc :: SharedContext s) => SharedTerm s
scTrue = scTrueTerm ?sc

scFalse :: (?sc :: SharedContext s) => SharedTerm s
scFalse = scFalseTerm ?sc

-- | Returns term as a constant Boolean if it can be evaluated as one.
scViewAsBool :: (?sc :: SharedContext s) => SharedTerm s -> Maybe Bool
scViewAsBool s | s == scTrue  = Just True
               | s == scFalse = Just False
               | otherwise = Nothing

-- | Returns term as an integer if it is an integer, signed bitvector, or unsigned
-- bitvector.
scViewAsNum :: (?sc :: SharedContext s) => SharedTerm s -> Maybe Integer
scViewAsNum = scViewAsNumFn ?sc

scPrettyTerm :: (?sc :: SharedContext s) => SharedTerm s -> String
scPrettyTerm t = show (scPrettyTermDocFn ?sc t)

-- 
data AppCache s = AC { acBindings :: !(Map (TermF (SharedTerm s)) (SharedTerm s))
                     , acNextIdx :: !Word64
                     }

emptyAppCache :: AppCache s
emptyAppCache = AC Map.empty 0

-- | Return term for application using existing term in cache if it is avaiable.
getTerm :: MVar (AppCache s) -> TermF (SharedTerm s) -> IO (SharedTerm s)
getTerm r a =
  modifyMVarMasked r $ \s -> do
    case Map.lookup a (acBindings s) of
      Just t -> return (s,t)
      Nothing -> seq s' $ return (s',t)
        where t = STApp (acNextIdx s) a
              s' = s { acBindings = Map.insert a t (acBindings s)
                     , acNextIdx = acNextIdx s + 1
                     }

{-
mkUninterpretedSharedContext :: IO (SharedContext s)
mkUninterpretedSharedContext = do
  cr <- newIORef emptyAppCache
  return SharedContext {
       scApplyFn = \f x -> getTerm cr (App f x)         
     , scLambdaFn = undefined
--     , scGlobalFn = undefined              
--     , scFreshGlobalFn = undefined
--     , scGlobalsWithType = undefined
--     , scLocalVarFn = undefined
--     , scBuiltinFn = undefined
     , scIntegerFn = undefined
     , scTypeOfFn  = undefined
--     , scViewFn = undefined
     , scPrettyTermDocFn = undefined
     , scMkRecordFn = undefined
     , scRecordSelectFn = undefined
     , scLoadModule = undefined
     }
-}

asIntLit :: SharedTerm s -> Maybe Integer
asIntLit (STApp _ (IntLit i)) = Just i
asIntLit _ = Nothing

asApp :: SharedTerm s -> Maybe (SharedTerm s, SharedTerm s)
asApp (STApp _ (App t u)) = Just (t,u)
asApp _ = Nothing

asApp3Of :: SharedTerm s -> SharedTerm s -> Maybe (SharedTerm s, SharedTerm s, SharedTerm s)
asApp3Of op s3 = do
  (s2,a3) <- asApp s3
  (s1,a2) <- asApp s2
  (s0,a1) <- asApp s1
  if s0 == op then return (a1,a2,a3) else fail ""

{-
data LocalVarTypeMap s = LVTM { lvtmMap :: Map Integer (SharedTerm s) }

consLocalVarType :: LocalVarTypeMap s -> Ident -> SharedTerm s -> LocalVarTypeMap s
consLocalVarType = undefined

localVarType :: DeBruijnIndex -> LocalVarTypeMap s -> SharedTerm s
localVarType = undefined
-}

data IOCache k v = IOCache !(MVar (Map k v)) (k -> IO v)

newIOCache :: (k -> IO v) -> IO (IOCache k v)
newIOCache fn = do
  mv <- newMVar Map.empty
  return (IOCache mv fn)  

getCacheValue :: Ord k => IOCache k v -> k -> IO v
getCacheValue (IOCache mv f) k = 
  modifyMVarMasked mv $ \m ->
    case Map.lookup k m of
      Just v -> return (m,v)
      Nothing -> fn <$> f k
        where fn v = (Map.insert k v m, v)        

data AppFns s = AppFns { defTypeCache :: IOCache (Def (SharedTerm s)) (SharedTerm s) }

mkApp :: (?af :: AppFns s) => TermF (SharedTerm s) -> IO (SharedTerm s)
mkApp = undefined

sharedDefType :: (?af :: AppFns s) => Def (SharedTerm s) -> IO (SharedTerm s)
sharedDefType = getCacheValue (defTypeCache ?af)

-- | Substitute var 0 in first term for second term, and shift all variable
-- references down.
subst0 :: (?af :: AppFns s) => SharedTerm s -> SharedTerm s -> IO (SharedTerm s)
subst0 = undefined

sortOfTerm :: (?af :: AppFns s) => SharedTerm s -> IO Sort
sortOfTerm t = do
  STApp _ (Sort s) <- typeOf t
  return s

mkSort :: (?af :: AppFns s) => Sort -> IO (SharedTerm s)
mkSort s = mkApp (Sort s)

typeOf :: (?af :: AppFns s)
       => SharedTerm s
       -> IO (SharedTerm s)
typeOf (STVar _ _ tp) = return tp
typeOf (STApp _ tf) =
  case tf of
    LocalVar _ tp -> return tp
    GlobalDef d -> sharedDefType d
    Lambda i tp rhs -> do
      rtp <- typeOf rhs
      mkApp (Pi i tp rtp)
    App x y -> do
      STApp _ (Pi _i _ rhs) <- typeOf x
      subst0 rhs y
    Pi _ tp rhs -> do
      ltp <- sortOfTerm tp
      rtp <- sortOfTerm rhs
      mkSort (max ltp rtp)
    TupleValue l  -> mkApp . TupleType =<< mapM typeOf l
    TupleType l  -> mkSort . maximum =<< mapM sortOfTerm l
    RecordValue m -> mkApp . RecordType =<< mapM typeOf m
    RecordSelector t f -> do
      STApp _ (RecordType m) <- typeOf t
      let Just tp = Map.lookup f m
      return tp
    RecordType m -> mkSort . maximum =<< mapM sortOfTerm m
    CtorValue c args -> undefined c args
    CtorType dt args -> undefined dt args
    Sort s -> mkSort (sortOf s)
    Let defs rhs -> undefined defs rhs
    IntLit i -> undefined i
    ArrayValue tp _ -> undefined tp
   
mkSharedContext :: Module -> IO (SharedContext s)
mkSharedContext m = do
  vr <- newMVar  0 -- ^ Reference for getting variables.
  cr <- newMVar emptyAppCache
  let getCtor sym args =
        case findCtor m (mkIdent sym) of
          Nothing -> fail $ "Failed to find " ++ show sym ++ " in module."
          Just c -> getTerm cr (CtorValue c args)
  let getDef sym =
        case findDef m (mkIdent sym) of
          Nothing -> fail $ "Failed to find " ++ show sym ++ " in module."
          Just d -> getTerm cr (GlobalDef (undefined d))
  trueTerm <- getCtor "True" []
  falseTerm <- getCtor "False" []
  let freshGlobal sym tp = do
        i <- modifyMVarMasked vr (\i -> return (i,i+1))
        return (STVar i sym tp)
  integerToSignedOp   <- getDef "integerToSigned"
  integerToUnsignedOp <- getDef "integerToUnsigned"
  let viewAsNum (asIntLit -> Just i) = Just i
      viewAsNum (asApp3Of integerToSignedOp -> Just (_,_,asIntLit -> Just i)) = Just i
      viewAsNum (asApp3Of integerToUnsignedOp -> Just (_,_,asIntLit -> Just i)) = Just i
      viewAsNum _ = Nothing
  tpCache <- newIOCache undefined
  let ?af = AppFns { defTypeCache = tpCache
                   }
  return SharedContext {
             scCurrentModuleFn = return m
           , scTrueTerm = trueTerm
           , scFalseTerm = falseTerm
           , scFreshGlobalFn = freshGlobal
           , scApplyFn = \f x -> undefined f x
           , scMkRecordFn = undefined
           , scRecordSelectFn = undefined
           , scIntegerFn = undefined
           , scTypeOfFn = typeOf
           , scPrettyTermDocFn = undefined
           , scViewAsNumFn = viewAsNum
           }

-- | Fold with memoization
foldSharedTerm :: forall s b . 
               (VarIndex -> Ident -> SharedTerm s -> b) 
               -> (TermF b -> b) -> SharedTerm s -> b
foldSharedTerm g f = \t -> State.evalState (go t) Map.empty
  where
    go :: SharedTerm s -> State.State (Map TermIndex b) b
    go (STVar i sym tp) = return $ g i sym tp
    go (STApp i t) = do
      memo <- State.get
      case Map.lookup i memo of
        Just x  -> return x
        Nothing -> do
          x <- fmap f (Traversable.mapM go t)
          State.modify (Map.insert i x)
          return x

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

{-
unshare :: SharedTerm s -> Term
unshare = foldSharedTerm Term
-}