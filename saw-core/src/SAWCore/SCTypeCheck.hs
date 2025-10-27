{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : SAWCore.SCTypeCheck
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.SCTypeCheck
  ( scTypeCheck
  , scTypeCheckError
  , scTypeCheckComplete
  , scTypeCheckCompleteError
  , SC.scTypeCheckWHNF
  , scConvertible
  , scCheckSubtype
  , TCError(..)
  , prettyTCError
  , throwTCError
  , TCM
  , runTCM
  , askCtx
  , withVar
  , withCtx
  , rethrowTCError
  , withEmptyTCState
  , atPos
  , LiftTCM(..)
  , TypeInfer(..)
  , typeCheckWHNF
  , typeInferCompleteWHNF
  , checkSubtype
  , ensureSort
  , applyPiTyped
  , compileRecursor
  ) where

import Control.Applicative
import Control.Monad (forM_, mapM, unless, void)
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), Reader, ReaderT(..), asks, runReader)
import Control.Monad.State.Strict (MonadState(..), StateT, evalStateT, modify)

import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Vector as V
import Prelude hiding (mapM, maximum)

import qualified SAWSupport.Pretty as PPS (defaultOpts)

import SAWCore.Module
  ( ctorName
  , dtName
  , lookupVarIndexInMap
  , Ctor(..)
  , DataType(..)
  , ResolvedName(..)
  )
import SAWCore.Name
import SAWCore.Parser.Position
import SAWCore.Recognizer
import qualified SAWCore.Term.Certified as SC
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (scPrettyTermInCtx)
import SAWCore.Term.Raw

-- | The state for a type-checking computation = a memoization table
type TCState = IntMap SC.Term

-- | The 'ReaderT' environment for a type-checking computation.
data TCEnv =
  TCEnv
  { tcSharedContext :: SharedContext -- ^ the SAW context
  , tcCtx :: IntMap Term             -- ^ the type environment for variables
  }

-- | The monad for type checking and inference, which:
--
-- * Maintains a 'SharedContext' and a variable context, where the
--   latter assigns types to the deBruijn indices in scope;
--
-- * Memoizes the most general type inferred for each expression; AND
--
-- * Can throw 'TCError's
newtype TCM a = TCM (ReaderT TCEnv (StateT TCState (ExceptT TCError IO)) a)
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO,
            MonadReader TCEnv, MonadState TCState, MonadError TCError)

-- | Run a type-checking computation in a given context, starting from the empty
-- memoization table
runTCM ::
  TCM a -> SharedContext -> IntMap Term -> IO (Either TCError a)
runTCM (TCM m) sc ctx =
  runExceptT $ evalStateT (runReaderT m (TCEnv sc ctx)) IntMap.empty

-- | Read the current typing context
askCtx :: TCM (IntMap Term)
askCtx = asks tcCtx

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given type. This throws away the memoization table while
-- running the sub-computation, as memoization tables are tied to specific sets
-- of bindings.
--
-- NOTE: the type given for the variable should be in WHNF, so that we do not
-- have to normalize the types of variables each time we see them.
withVar :: VarName -> Term -> TCM a -> TCM a
withVar x tp m =
  rethrowTCError (ErrorCtx (vnName x) tp) $
  withEmptyTCState $
  local (\env -> env { tcCtx = IntMap.insert (vnIndex x) tp (tcCtx env) }) m

-- | Run a type-checking computation in a typing context extended by a list of
-- variables and their types. See 'withVar'.
withCtx :: [(VarName, Term)] -> TCM a -> TCM a
withCtx = flip (foldr (\(x,tp) -> withVar x tp))

-- | Augment and rethrow any 'TCError' thrown by the given computation.
rethrowTCError :: (MonadError TCError m) => (TCError -> TCError) -> m a -> m a
rethrowTCError f m = catchError m (throwError . f)

-- | Clear the memoization table before running the sub-computation,
-- and restore it afterward.
withEmptyTCState :: (MonadState TCState m) => m a -> m a
withEmptyTCState m =
  do saved_table <- get
     put IntMap.empty
     a <- m
     put saved_table
     pure a

-- | Run a type-checking computation @m@ and tag any error it throws with the
-- 'ErrorTerm' constructor
withErrorTerm :: Term -> TCM a -> TCM a
withErrorTerm tm m = catchError m (throwError . ErrorTerm tm)

-- | Lift @withErrorTerm@ to `TermF Term`
withErrorTermF :: TermF Term -> TCM a -> TCM a
withErrorTermF tm = withErrorTerm (Unshared tm)

-- | Lift @withErrorTerm@ to `TermF SC.Term`
withErrorCTermF :: TermF SC.Term -> TCM a -> TCM a
withErrorCTermF tm = withErrorTermF (fmap SC.rawTerm tm)

-- | Run a type-checking computation @m@ and tag any error it throws with the
-- given position, using the 'ErrorPos' constructor, unless that error is
-- already tagged with a position
atPos :: (MonadError TCError m) => Pos -> m a -> m a
atPos p = rethrowTCError (ErrorPos p)

-- | Typeclass for lifting 'IO' computations that take a 'SharedContext' to
-- 'TCM' computations
class LiftTCM a where
  type TCMLifted a
  liftTCM :: (SharedContext -> a) -> TCMLifted a

instance LiftTCM (IO a) where
  type TCMLifted (IO a) = TCM a
  liftTCM f =
    do sc <- asks tcSharedContext
       liftIO (f sc)

instance LiftTCM b => LiftTCM (a -> b) where
  type TCMLifted (a -> b) = a -> TCMLifted b
  liftTCM f a = liftTCM (\sc -> f sc a)

-- | Errors that can occur during type-checking
data TCError
  = NotSort Term
  | NotFuncTypeInApp SC.Term SC.Term
  | NotTupleType Term
  | BadTupleIndex Int Term
  | NotRecordType SC.Term
  | BadRecordField FieldName Term
  | DanglingVar Int
  | UnboundName Text
  | SubtypeFailure SC.Term Term
  | EmptyVectorLit
  | NoSuchDataType NameInfo
  | NoSuchCtor NameInfo
  | NoSuchConstant NameInfo
  | NotFullyAppliedRec NameInfo
  | MalformedRecursor Term String
  | DeclError Text String
  | ErrorPos Pos TCError
  | ErrorCtx LocalName Term TCError
  | ErrorTerm Term TCError
  | ExpectedRecursor SC.Term


-- | Throw a type-checking error
throwTCError :: (MonadError TCError m) => TCError -> m a
throwTCError e = throwError e

type PPErrM = Reader ([LocalName], Maybe Pos)

-- | Pretty-print a type-checking error
prettyTCError :: TCError -> [String]
prettyTCError e = runReader (helper e) ([], Nothing) where

  ppWithPos :: [PPErrM String] -> PPErrM [String]
  ppWithPos str_ms =
    do strs <- mapM id str_ms
       (_, maybe_p) <- ask
       case maybe_p of
         Just p -> return (ppPos p : strs)
         Nothing -> return strs

  helper :: TCError -> PPErrM [String]
  helper (NotSort ty) = ppWithPos [ return "Not a sort" , ishow ty ]
  helper (NotFuncTypeInApp f arg) =
      ppWithPos [ return "Function application with non-function type"
                , return "For term:"
                , ishow (SC.rawTerm f)
                , return "With type:"
                , ishow (SC.rawType f)
                , return "To argument:"
                , ishow (SC.rawTerm arg) ]
  helper (NotTupleType ty) =
      ppWithPos [ return "Tuple field projection with non-tuple type" ,
                  ishow ty ]
  helper (BadTupleIndex n ty) =
      ppWithPos [ return ("Bad tuple index (" ++ show n ++ ") for type")
                , ishow ty ]
  helper (NotRecordType t) =
      ppWithPos [ return "Record field projection with non-record type"
                , ishow (SC.rawType t)
                , return "In term:"
                , ishow (SC.rawTerm t) ]
  helper (BadRecordField n ty) =
      ppWithPos [ return ("Bad record field (" ++ show n ++ ") for type")
                , ishow ty ]
  helper (DanglingVar n) =
      ppWithPos [ return ("Dangling bound variable index: " ++ show n)]
  helper (UnboundName str) = ppWithPos [ return ("Unbound name: " ++ show str)]
  helper (SubtypeFailure trm tp2) =
      ppWithPos [ return "Inferred type", ishow (SC.rawType trm),
                  return "Not a subtype of expected type", ishow tp2,
                  return "For term", ishow (SC.rawTerm trm) ]
  helper EmptyVectorLit = ppWithPos [ return "Empty vector literal"]
  helper (NoSuchDataType d) =
    ppWithPos [ return ("No such data type: " ++ show d)]
  helper (NoSuchCtor c) =
    ppWithPos [ return ("No such constructor: " ++ show c) ]
  helper (NoSuchConstant c) =
    ppWithPos [ return ("No such constant: " ++ show c) ]
  helper (NotFullyAppliedRec i) =
      ppWithPos [ return ("Recursor not fully applied: " ++ show i) ]
  helper (MalformedRecursor trm reason) =
      ppWithPos [ return "Malformed recursor",
                  ishow trm, return reason ]
  helper (DeclError nm reason) =
    ppWithPos [ return ("Malformed declaration for " ++ show nm), return reason ]
  helper (ErrorPos p err) =
    local (\(ctx,_) -> (ctx, Just p)) $ helper err
  helper (ErrorCtx x _ err) =
    local (\(ctx,p) -> (x:ctx, p)) $ helper err
  helper (ErrorTerm tm err) = do
    info <- ppWithPos [ return ("While typechecking term:")
                      , ishow tm ]
    cont <- helper err
    return (info ++ cont)
  helper (ExpectedRecursor ttm) =
    ppWithPos [ return "Expected recursor value", ishow (SC.rawTerm ttm), ishow (SC.rawType ttm)]

  -- | Add prefix to every line, but remove final trailing newline
  indent :: String -> String -> String
  indent prefix s = init (unlines (map (prefix ++) (lines s)))

  ishow :: Term -> PPErrM String
  ishow tm =
    -- return $ show tm
    (\(_ctx,_) -> indent "  " $ scPrettyTermInCtx PPS.defaultOpts [] tm) <$> ask

instance Show TCError where
  show = unlines . prettyTCError

-- | Infer the type of a term using 'scTypeCheck', calling 'fail' on failure
scTypeCheckError :: TypeInfer a => SharedContext -> a -> IO Term
scTypeCheckError sc t0 =
  either (fail . unlines . prettyTCError) return =<< scTypeCheck sc t0

-- | Infer the type of a 'Term', ensuring in the process that the entire term is
-- well-formed and that all internal type annotations are correct. Types are
-- evaluated to WHNF as necessary, and the returned type is in WHNF.
scTypeCheck :: TypeInfer a => SharedContext -> a -> IO (Either TCError Term)
scTypeCheck sc = scTypeCheckInCtx sc IntMap.empty

-- | Like 'scTypeCheck', but type-check the term relative to a typing context,
-- which assigns types to free variables in the term
scTypeCheckInCtx ::
  TypeInfer a => SharedContext ->
  IntMap Term -> a -> IO (Either TCError Term)
scTypeCheckInCtx sc ctx t0 = runTCM (typeInfer t0) sc ctx

-- | Infer the type of an @a@ and complete it to a term using
-- 'scTypeCheckComplete', calling 'fail' on failure
scTypeCheckCompleteError ::
  TypeInfer a => SharedContext -> a -> IO SC.Term
scTypeCheckCompleteError sc t0 =
  either (fail . unlines . prettyTCError) return =<<
  scTypeCheckComplete sc t0

-- | Infer the type of an @a@ and complete it to a term, ensuring in the
-- process that the entire term is well-formed and that all internal type
-- annotations are correct. Types are evaluated to WHNF as necessary, and the
-- returned type is in WHNF, though the returned term may not be.
scTypeCheckComplete ::
  TypeInfer a => SharedContext -> a -> IO (Either TCError SC.Term)
scTypeCheckComplete sc = scTypeCheckCompleteInCtx sc IntMap.empty

-- | Like 'scTypeCheckComplete', but type-check the term relative to a typing
-- context, which assigns types to free variables in the term
scTypeCheckCompleteInCtx :: TypeInfer a => SharedContext ->
                            IntMap Term -> a ->
                            IO (Either TCError SC.Term)
scTypeCheckCompleteInCtx sc ctx t0 =
  runTCM (typeInferComplete t0) sc ctx

-- | Check that one type is a subtype of another using 'checkSubtype', calling
-- 'fail' on failure
scCheckSubtype :: SharedContext -> SC.Term -> Term -> IO ()
scCheckSubtype sc arg req_tp =
  either (fail . unlines . prettyTCError) return =<<
  runTCM (checkSubtype arg req_tp) sc IntMap.empty

-- | The class of things that we can infer types of. The 'typeInfer' method
-- returns the most general (with respect to subtyping) type of its input.
class TypeInfer a where
  -- | Infer the type of an @a@
  typeInfer :: a -> TCM Term
  -- | Infer the type of an @a@ and complete it to a 'Term'
  typeInferComplete :: a -> TCM SC.Term

-- | Infer the type of an @a@ and complete it to a 'Term', and then evaluate the
-- resulting term to WHNF
typeInferCompleteWHNF :: TypeInfer a => a -> TCM SC.Term
typeInferCompleteWHNF a =
  do t <- typeInferComplete a
     liftTCM SC.scWHNF t

-- Type inference for Term dispatches to type inference on TermF Term, but uses
-- memoization to avoid repeated work
instance TypeInfer Term where
  typeInfer t = SC.rawType <$> typeInferComplete t
  typeInferComplete t =
    case t of
      Unshared tf ->
        withErrorTerm t $ typeInferComplete tf
      STApp{stAppIndex = i, stAppTermF = tf} ->
        do table <- get
           case IntMap.lookup i table of
             Just x -> pure x
             Nothing ->
               do x <- withErrorTerm t $ typeInferComplete tf
                  modify (IntMap.insert i x)
                  pure x

-- Type inference for TermF Term dispatches to that for TermF SC.Term by
-- calling inference on all the sub-components and extending the context inside
-- of the binding forms
instance TypeInfer (TermF Term) where
  typeInfer tf = SC.rawType <$> typeInferComplete tf
  typeInferComplete tf =
    case tf of
      FTermF ftf ->
        -- Dispatch to the TypeInfer instance for FlatTermF Term
        do typeInferComplete ftf
      App t1 t2 ->
        do t1t <- typeInferComplete t1
           t2t <- typeInferComplete t2
           inferTermF (App t1t t2t)
      Lambda x t1 t2 ->
        do t1t <- typeInferComplete t1
           t2t <- withVar x (SC.rawTerm t1t) $ typeInferComplete t2
           inferTermF (Lambda x t1t t2t)
      Pi x t1 t2 ->
        do t1t <- typeInferComplete t1
           t2t <- withVar x (SC.rawTerm t1t) $ typeInferComplete t2
           inferTermF (Pi x t1t t2t)
      Constant nm ->
        do inferTermF (Constant nm)
      Variable x t1 ->
        do t1t <- typeInferComplete t1
           inferTermF (Variable x t1t)

-- Type inference for FlatTermF Term dispatches to that for FlatTermF SC.Term.
instance TypeInfer (FlatTermF Term) where
  typeInfer ftf = SC.rawType <$> typeInferComplete ftf
  typeInferComplete ftf =
    typeInferComplete =<< mapM typeInferComplete ftf

-- Type inference for TermF SC.Term is the main workhorse. Intuitively, this
-- represents the case where each immediate subterm of a term is labeled with
-- its (most general) type.
instance TypeInfer (TermF SC.Term) where
  typeInfer tf = SC.rawType <$> typeInferComplete tf
  typeInferComplete tf =
    withErrorCTermF tf (inferTermF tf)

-- Type inference for FlatTermF SC.Term is the main workhorse for flat
-- terms. Intuitively, this represents the case where each immediate subterm of
-- a term has already been labeled with its (most general) type.
instance TypeInfer (FlatTermF SC.Term) where
  typeInfer ftf =
    SC.rawType <$> inferFlatTermF ftf
  typeInferComplete ftf =
    withErrorCTermF (FTermF ftf) (inferFlatTermF ftf)

-- | Construct a typed term from a 'TermF' where each subterm has
-- already been labeled with its type.
inferTermF :: TermF SC.Term -> TCM SC.Term
inferTermF tf =
  case tf of
    FTermF ftf ->
      inferFlatTermF ftf
    App t1 t2 ->
      do let err = NotFuncTypeInApp t1 t2
         (_nm, arg_tp, _ret_tp) <- ensurePiType err (SC.rawType t1)
         checkSubtype t2 arg_tp
         liftTCM SC.scApply t1 t2
    Lambda x t1 t2 ->
      do void $ ensureSort (SC.rawType t1)
         liftTCM SC.scLambda x t1 t2
    Pi x t1 t2 ->
      do void $ ensureSort (SC.rawType t1)
         void $ ensureSort (SC.rawType t2)
         liftTCM SC.scPi x t1 t2
    Constant nm ->
      do mm <- liftTCM scGetModuleMap
         case lookupVarIndexInMap (nameIndex nm) mm of
           Nothing -> throwTCError $ NoSuchConstant (nameInfo nm)
           Just _ -> liftTCM SC.scConstant nm
    Variable vn tp ->
      liftTCM SC.scVariable vn tp

-- | Construct a typed term from a 'FlatTermF' where each subterm has
-- already been labeled with its type.
inferFlatTermF :: FlatTermF SC.Term -> TCM SC.Term
inferFlatTermF ftf =
  case ftf of
    UnitValue ->
      liftTCM SC.scUnitValue
    UnitType ->
      liftTCM SC.scUnitType
    PairValue t1 t2 ->
      liftTCM SC.scPairValue t1 t2
    PairType t1 t2 ->
      do void $ ensureSort (SC.rawType t1)
         void $ ensureSort (SC.rawType t2)
         liftTCM SC.scPairType t1 t2
    PairLeft t ->
      do void $ ensurePairType (SC.rawType t)
         liftTCM SC.scPairLeft t
    PairRight t ->
      do void $ ensurePairType (SC.rawType t)
         liftTCM SC.scPairRight t
    Recursor r ->
      do mm <- liftTCM scGetModuleMap
         let d = recursorDataType r
         let s = recursorSort r
         case lookupVarIndexInMap (nameIndex d) mm of
           Just (ResolvedDataType _dt) -> liftTCM SC.scRecursor d s
           _ -> throwTCError $ NoSuchDataType (nameInfo d)
    RecordType elems ->
      do void $ mapM (ensureSort . SC.rawType . snd) elems
         liftTCM SC.scRecordType elems
    RecordValue elems ->
      liftTCM SC.scRecordValue elems
    RecordProj t fld ->
      do ts <- ensureRecordType (NotRecordType t) (SC.rawType t)
         unless (Map.member fld ts) $
           throwTCError $ BadRecordField fld (SC.rawType t)
         liftTCM SC.scRecordProj t fld
    Sort s flags ->
      liftTCM SC.scSortWithFlags s flags
    NatLit n ->
      liftTCM SC.scNat n
    ArrayValue tp vs ->
      do void $ ensureSort (SC.rawType tp)
         tp' <- typeCheckWHNF (SC.rawTerm tp)
         forM_ vs $ \v_elem -> checkSubtype v_elem tp'
         liftTCM SC.scVector tp (V.toList vs)
    StringLit s ->
      liftTCM SC.scString s

-- | Check that @fun_tp=Pi x a b@ and that @arg@ has type @a@, and return the
-- result of substituting @arg@ for @x@ in the result type @b@, i.e.,
-- @[arg/x]b@.
-- If @fun_tp@ is not a pi type, raise the supplied error.
applyPiTyped :: TCError -> Term -> SC.Term -> TCM Term
applyPiTyped err fun_tp arg =
  ensurePiType err fun_tp >>= \(nm, arg_tp, ret_tp) ->
  do checkSubtype arg arg_tp
     let sub = IntMap.singleton (vnIndex nm) (SC.rawTerm arg)
     liftTCM scInstantiateExt sub ret_tp

-- | Ensure that a 'Term' matches a recognizer function, normalizing if
-- necessary; otherwise throw the supplied 'TCError'
ensureRecognizer :: Recognizer Term a -> TCError -> Term -> TCM a
ensureRecognizer f _ (f -> Just a) = return a
ensureRecognizer f err trm =
  typeCheckWHNF trm >>= \case
  (f -> Just a) -> return a
  _ -> throwTCError err

-- | Ensure a 'Term' is a sort, normalizing if necessary, and return that sort
ensureSort :: Term -> TCM Sort
ensureSort tp = ensureRecognizer asSort (NotSort tp) tp

-- | Ensure a 'Term' is a pair type, normalizing if necessary, and return the
-- two components of that pair type
ensurePairType :: Term -> TCM (Term, Term)
ensurePairType tp = ensureRecognizer asPairType (NotTupleType tp) tp

-- | Ensure a 'Term' is a record type, normalizing if necessary, and return the
-- components of that record type
ensureRecordType :: TCError -> Term -> TCM (Map FieldName Term)
ensureRecordType err tp = ensureRecognizer asRecordType err tp

-- | Ensure a 'Term' is a pi type, normalizing if necessary. Return the
-- components of that pi type on success; otherwise throw the supplied error.
ensurePiType :: TCError -> Term -> TCM (VarName, Term, Term)
ensurePiType err tp = ensureRecognizer asPi err tp

-- | Reduce a type to WHNF (using 'scWhnf'), also adding in some conversions for
-- operations on Nat literals that are useful in type-checking
typeCheckWHNF :: Term -> TCM Term
typeCheckWHNF = liftTCM SC.scTypeCheckWHNF

-- | Check that one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s.
checkSubtype :: SC.Term -> Term -> TCM ()
checkSubtype arg req_tp =
  do arg_tp' <- liftTCM scWhnf (SC.rawType arg)
     req_tp' <- liftTCM scWhnf req_tp
     ok <- isSubtype arg_tp' req_tp'
     if ok then return () else throwTCError $ SubtypeFailure arg req_tp

-- | Check if one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s, and that they are both
-- already in WHNF
isSubtype :: Term -> Term -> TCM Bool
isSubtype (unwrapTermF -> Pi x1 a1 b1) (unwrapTermF -> Pi x2 a2 b2)
  | x1 == x2 =
    (&&) <$> areConvertible a1 a2 <*> withVar x1 a1 (isSubtype b1 b2)
  | otherwise =
    do conv1 <- areConvertible a1 a2
       var1 <- liftTCM scVariable x1 a1
       let sub = IntMap.singleton (vnIndex x2) var1
       b2' <- liftTCM scInstantiateExt sub b2
       conv2 <- withVar x1 a1 (isSubtype b1 b2')
       pure (conv1 && conv2)
isSubtype (asSort -> Just s1) (asSort -> Just s2) | s1 <= s2 = return True
isSubtype t1' t2' = areConvertible t1' t2'

-- | Check if two terms are "convertible for type-checking", meaning that they
-- are convertible up to 'natConversions'
areConvertible :: Term -> Term -> TCM Bool
areConvertible t1 t2 = liftTCM scConvertibleEval SC.scTypeCheckWHNF True t1 t2


compileRecursor ::
  DataType ->
  Sort          {- ^ elimination sort -} ->
  TCM CompiledRecursor
compileRecursor dt s =
  do let d = dtName dt
     let nparams = length (dtParams dt)
     let nixs = length (dtIndices dt)
     let ctorOrder = map ctorName (dtCtors dt)
     let crec = CompiledRecursor d s nparams nixs ctorOrder

     -- Check that the parameters are correct for the given datatype
     let err =
           MalformedRecursor
           (Unshared $ fmap SC.rawTerm $ FTermF $ Recursor crec)
           "Disallowed propositional elimination"

     unless (allowedElimSort dt s) $ throwTCError err
     return crec
