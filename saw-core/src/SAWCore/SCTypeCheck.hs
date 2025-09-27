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
  , scTypeCheckWHNF
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
  , SCTypedTerm -- abstract
  , typedVal
  , typedType
  , typedCtx
  , TypeInfer(..)
  , typeCheckWHNF
  , typeInferCompleteWHNF
  , checkSubtype
  , ensureSort
  , applyPiTyped
  , compileRecursor
  , scTypeOfTypedTerm
  , scTypedTermWHNF
  , scGlobalTypedTerm
  ) where

import Control.Applicative
import Control.Monad (foldM, forM_, mapM, unless, void)
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), Reader, ReaderT(..), asks, runReader)
import Control.Monad.State.Strict (MonadState(..), StateT, evalStateT, modify)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Vector as V
import Prelude hiding (mapM, maximum)

import qualified SAWSupport.Pretty as PPS (defaultOpts)

import SAWCore.Conversion (natConversions)
import SAWCore.Module
  ( ctorName
  , dtName
  , lookupVarIndexInMap
  , resolvedNameType
  , Ctor(..)
  , DataType(..)
  )
import SAWCore.Name
import SAWCore.Parser.Position
import SAWCore.Recognizer
import SAWCore.Rewriter
import SAWCore.SharedTerm
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (scPrettyTermInCtx)

-- | The state for a type-checking computation = a memoization table
type TCState = Map TermIndex Term

-- | The 'ReaderT' environment for a type-checking computation.
data TCEnv =
  TCEnv
  { tcSharedContext :: SharedContext -- ^ the SAW context
  , tcCtx :: [(LocalName, Term)]     -- ^ the mapping of names to de Bruijn bound variables
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
  TCM a -> SharedContext -> [(LocalName, Term)] -> IO (Either TCError a)
runTCM (TCM m) sc ctx =
  runExceptT $ evalStateT (runReaderT m (TCEnv sc ctx)) Map.empty

-- | Read the current typing context
askCtx :: TCM [(LocalName, Term)]
askCtx = asks tcCtx

-- | Read the current typing context, without names.
askCtx' :: TCM [Term]
askCtx' = map snd <$> askCtx

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given type. This throws away the memoization table while
-- running the sub-computation, as memoization tables are tied to specific sets
-- of bindings.
--
-- NOTE: the type given for the variable should be in WHNF, so that we do not
-- have to normalize the types of variables each time we see them.
withVar :: LocalName -> Term -> TCM a -> TCM a
withVar x tp m =
  rethrowTCError (ErrorCtx x tp) $
  withEmptyTCState $
  local (\env -> env { tcCtx = (x,tp) : tcCtx env }) m

-- | Run a type-checking computation in a typing context extended by a list of
-- variables and their types. See 'withVar'.
withCtx :: [(LocalName, Term)] -> TCM a -> TCM a
withCtx = flip (foldr (\(x,tp) -> withVar x tp))

-- | Augment and rethrow any 'TCError' thrown by the given computation.
rethrowTCError :: (MonadError TCError m) => (TCError -> TCError) -> m a -> m a
rethrowTCError f m = catchError m (throwError . f)

-- | Clear the memoization table before running the sub-computation,
-- and restore it afterward.
withEmptyTCState :: (MonadState TCState m) => m a -> m a
withEmptyTCState m =
  do saved_table <- get
     put Map.empty
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

-- | Lift @withErrorTerm@ to `TermF SCTypedTerm`
withErrorSCTypedTermF :: TermF SCTypedTerm -> TCM a -> TCM a
withErrorSCTypedTermF tm = withErrorTermF (fmap typedVal tm)

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
  | NotFuncTypeInApp SCTypedTerm SCTypedTerm
  | NotTupleType Term
  | BadTupleIndex Int Term
  | NotRecordType SCTypedTerm
  | BadRecordField FieldName Term
  | DanglingVar Int
  | UnboundName Text
  | SubtypeFailure SCTypedTerm Term
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
  | ExpectedRecursor SCTypedTerm


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
                , ishow (typedVal f)
                , return "With type:"
                , ishow (typedType f)
                , return "To argument:"
                , ishow (typedVal arg) ]
  helper (NotTupleType ty) =
      ppWithPos [ return "Tuple field projection with non-tuple type" ,
                  ishow ty ]
  helper (BadTupleIndex n ty) =
      ppWithPos [ return ("Bad tuple index (" ++ show n ++ ") for type")
                , ishow ty ]
  helper (NotRecordType (SCTypedTerm trm tp _ctx)) =
      ppWithPos [ return "Record field projection with non-record type"
                , ishow tp
                , return "In term:"
                , ishow trm ]
  helper (BadRecordField n ty) =
      ppWithPos [ return ("Bad record field (" ++ show n ++ ") for type")
                , ishow ty ]
  helper (DanglingVar n) =
      ppWithPos [ return ("Dangling bound variable index: " ++ show n)]
  helper (UnboundName str) = ppWithPos [ return ("Unbound name: " ++ show str)]
  helper (SubtypeFailure trm tp2) =
      ppWithPos [ return "Inferred type", ishow (typedType trm),
                  return "Not a subtype of expected type", ishow tp2,
                  return "For term", ishow (typedVal trm) ]
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
    ppWithPos [ return "Expected recursor value", ishow (typedVal ttm), ishow (typedType ttm)]

  -- | Add prefix to every line, but remove final trailing newline
  indent :: String -> String -> String
  indent prefix s = init (unlines (map (prefix ++) (lines s)))

  ishow :: Term -> PPErrM String
  ishow tm =
    -- return $ show tm
    (\(ctx,_) -> indent "  " $ scPrettyTermInCtx PPS.defaultOpts ctx tm) <$> ask

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
scTypeCheck sc = scTypeCheckInCtx sc []

-- | Like 'scTypeCheck', but type-check the term relative to a typing context,
-- which assigns types to free variables in the term
scTypeCheckInCtx ::
  TypeInfer a => SharedContext ->
  [(LocalName, Term)] -> a -> IO (Either TCError Term)
scTypeCheckInCtx sc ctx t0 = runTCM (typeInfer t0) sc ctx

-- | Infer the type of an @a@ and complete it to a term using
-- 'scTypeCheckComplete', calling 'fail' on failure
scTypeCheckCompleteError ::
  TypeInfer a => SharedContext -> a -> IO SCTypedTerm
scTypeCheckCompleteError sc t0 =
  either (fail . unlines . prettyTCError) return =<<
  scTypeCheckComplete sc t0

-- | Infer the type of an @a@ and complete it to a term, ensuring in the
-- process that the entire term is well-formed and that all internal type
-- annotations are correct. Types are evaluated to WHNF as necessary, and the
-- returned type is in WHNF, though the returned term may not be.
scTypeCheckComplete ::
  TypeInfer a => SharedContext -> a -> IO (Either TCError SCTypedTerm)
scTypeCheckComplete sc = scTypeCheckCompleteInCtx sc []

-- | Like 'scTypeCheckComplete', but type-check the term relative to a typing
-- context, which assigns types to free variables in the term
scTypeCheckCompleteInCtx :: TypeInfer a => SharedContext ->
                            [(LocalName, Term)] -> a ->
                            IO (Either TCError SCTypedTerm)
scTypeCheckCompleteInCtx sc ctx t0 =
  runTCM (typeInferComplete t0) sc ctx

-- | Check that one type is a subtype of another using 'checkSubtype', calling
-- 'fail' on failure
scCheckSubtype :: SharedContext -> SCTypedTerm -> Term -> IO ()
scCheckSubtype sc arg req_tp =
  either (fail . unlines . prettyTCError) return =<<
  runTCM (checkSubtype arg req_tp) sc []

-- | An abstract datatype pairing a 'Term' with its type.
data SCTypedTerm =
  SCTypedTerm
  Term -- ^ value
  Term -- ^ type
  [Term] -- ^ de Bruijn typing context

-- | The raw 'Term' of an 'SCTypedTerm'.
typedVal :: SCTypedTerm -> Term
typedVal (SCTypedTerm trm _ _) = trm

-- | The type of an 'SCTypedTerm' as a 'Term'.
typedType :: SCTypedTerm -> Term
typedType (SCTypedTerm _ typ _) = typ

-- | The de Bruijn typing context of an 'SCTypedTerm', with de Bruijn
-- index 0 at the head of the list.
typedCtx :: SCTypedTerm -> [Term]
typedCtx (SCTypedTerm _ _ ctx) = ctx

-- | The class of things that we can infer types of. The 'typeInfer' method
-- returns the most general (with respect to subtyping) type of its input.
class TypeInfer a where
  -- | Infer the type of an @a@
  typeInfer :: a -> TCM Term
  -- | Infer the type of an @a@ and complete it to a 'Term'
  typeInferComplete :: a -> TCM SCTypedTerm

-- | Infer the type of an @a@ and complete it to a 'Term', and then evaluate the
-- resulting term to WHNF
typeInferCompleteWHNF :: TypeInfer a => a -> TCM SCTypedTerm
typeInferCompleteWHNF a =
  do SCTypedTerm a_trm a_tp ctx <- typeInferComplete a
     a_whnf <- typeCheckWHNF a_trm
     return $ SCTypedTerm a_whnf a_tp ctx


-- Type inference for Term dispatches to type inference on TermF Term, but uses
-- memoization to avoid repeated work
instance TypeInfer Term where
  typeInfer t@(Unshared tf) = withErrorTerm t $ typeInfer tf
  typeInfer t@(STApp{ stAppIndex = i, stAppTermF = tf}) =
    do table <- TCM get
       case Map.lookup i table of
         Just x  -> return x
         Nothing ->
           do x  <- withErrorTerm t $ typeInfer tf
              x' <- typeCheckWHNF x
              modify (Map.insert i x')
              return x'
  typeInferComplete trm =
    SCTypedTerm trm <$> typeInfer trm <*> askCtx'

-- Type inference for TermF Term dispatches to that for TermF SCTypedTerm by
-- calling inference on all the sub-components and extending the context inside
-- of the binding forms
instance TypeInfer (TermF Term) where
  typeInfer (FTermF ftf) =
    -- Dispatch to the TypeInfer instance for FlatTermF Term, which does some
    -- special-case handling itself
    typeInfer ftf
  typeInfer (Lambda x a rhs) =
    do a_whnf <- typeInferCompleteWHNF a
       -- NOTE: before adding a type to the context, we want to be sure it is in
       -- WHNF, so we don't have to normalize each time we look up a var type,
       -- but we want to leave the non-normalized value of a in the returned
       -- term, so we create a_tptrm with the type of a_whnf but the value of a
       rhs_tptrm <- withVar x (typedVal a_whnf) $ typeInferComplete rhs
       let a_tptrm = SCTypedTerm a (typedType a_whnf) (typedCtx a_whnf)
       typeInfer (Lambda x a_tptrm rhs_tptrm)
  typeInfer (Pi x a rhs) =
    do a_whnf <- typeInferCompleteWHNF a
       -- NOTE: before adding a type to the context, we want to be sure it is in
       -- WHNF, so we don't have to normalize each time we look up a var type,
       -- but we want to leave the non-normalized value of a in the returned
       -- term, so we create a_typed with the type of a_whnf but the value of a
       rhs_tptrm <- withVar x (typedVal a_whnf) $ typeInferComplete rhs
       let a_tptrm = SCTypedTerm a (typedType a_whnf) (typedCtx a_whnf)
       typeInfer (Pi x a_tptrm rhs_tptrm)
  typeInfer (Constant nm) = typeInferConstant nm
  typeInfer t = typeInfer =<< mapM typeInferComplete t
  typeInferComplete tf =
    SCTypedTerm <$> liftTCM scTermF tf <*> withErrorTermF tf (typeInfer tf) <*> askCtx'

typeInferConstant :: Name -> TCM Term
typeInferConstant nm =
  do mm <- liftTCM scGetModuleMap
     case lookupVarIndexInMap (nameIndex nm) mm of
       Just r -> pure (resolvedNameType r)
       Nothing -> throwTCError $ NoSuchConstant (nameInfo nm)

-- Type inference for FlatTermF Term dispatches to that for FlatTermF SCTypedTerm,
-- with special cases for primitives and constants to avoid re-type-checking
-- their types as we are assuming they were type-checked when they were created
instance TypeInfer (FlatTermF Term) where
  typeInfer t = typeInfer =<< mapM typeInferComplete t
  typeInferComplete ftf =
    SCTypedTerm
    <$> liftTCM scFlatTermF ftf
    <*> typeInfer ftf
    <*> askCtx'


-- Type inference for TermF SCTypedTerm is the main workhorse. Intuitively, this
-- represents the case where each immediate subterm of a term is labeled with
-- its (most general) type.
instance TypeInfer (TermF SCTypedTerm) where
  typeInfer (FTermF ftf) = typeInfer ftf
  typeInfer (App x@(SCTypedTerm _ x_tp _) y) =
    applyPiTyped (NotFuncTypeInApp x y) x_tp y
  typeInfer (Lambda x (SCTypedTerm a a_tp _) (SCTypedTerm _ b _)) =
    void (ensureSort a_tp) >> liftTCM scTermF (Pi x a b)
  typeInfer (Pi _ (SCTypedTerm _ a_tp _) (SCTypedTerm _ b_tp _)) =
    do s1 <- ensureSort a_tp
       s2 <- ensureSort b_tp
       -- NOTE: the rule for type-checking Pi types is that (Pi x a b) is a Prop
       -- when b is a Prop (this is a forall proposition), otherwise it is a
       -- (Type (max (sortOf a) (sortOf b)))
       liftTCM scSort $ if s2 == propSort then propSort else max s1 s2
  typeInfer (LocalVar i) =
    do ctx <- askCtx
       if i < length ctx then
         -- The ith type in the current variable typing context is well-typed
         -- relative to the suffix of the context after it, so we have to lift it
         -- (i.e., call incVars) to make it well-typed relative to all of ctx
         liftTCM incVars 0 (i+1) (snd (ctx !! i))
         else
         error ("Context = " ++ show ctx)
         -- throwTCError (DanglingVar (i - length ctx))
  typeInfer (Constant nm) = typeInferConstant nm
  typeInfer (Variable ec) =
    -- FIXME: should we check that the type of ecType is a sort?
    typeCheckWHNF $ typedVal $ ecType ec

  typeInferComplete tf =
    SCTypedTerm
    <$> liftTCM scTermF (fmap typedVal tf)
    <*> withErrorSCTypedTermF tf (typeInfer tf)
    <*> askCtx'


-- Type inference for FlatTermF SCTypedTerm is the main workhorse for flat
-- terms. Intuitively, this represents the case where each immediate subterm of
-- a term has already been labeled with its (most general) type.
instance TypeInfer (FlatTermF SCTypedTerm) where
  typeInfer UnitValue = liftTCM scUnitType
  typeInfer UnitType = liftTCM scSort (mkSort 0)
  typeInfer (PairValue (SCTypedTerm _ tx _) (SCTypedTerm _ ty _)) =
    liftTCM scPairType tx ty
  typeInfer (PairType (SCTypedTerm _ tx _) (SCTypedTerm _ ty _)) =
    do sx <- ensureSort tx
       sy <- ensureSort ty
       liftTCM scSort (max sx sy)
  typeInfer (PairLeft (SCTypedTerm _ tp _)) =
    ensurePairType tp >>= \(t1,_) -> return t1
  typeInfer (PairRight (SCTypedTerm _ tp _)) =
    ensurePairType tp >>= \(_,t2) -> return t2

  typeInfer (Recursor crec) =
    inferRecursor crec

  typeInfer (RecordType elems) =
    -- NOTE: record types are always predicative, i.e., non-Propositional, so we
    -- ensure below that we return at least sort 0
    do sorts <- mapM (ensureSort . typedType . snd) elems
       liftTCM scSort (maxSort $ mkSort 0 : sorts)
  typeInfer (RecordValue elems) =
    liftTCM scFlatTermF $ RecordType $
    map (\(f,SCTypedTerm _ tp _) -> (f,tp)) elems
  typeInfer (RecordProj t@(SCTypedTerm _ t_tp _) fld) =
    ensureRecordType (NotRecordType t) t_tp >>= \case
    (Map.lookup fld -> Just tp) -> return tp
    _ -> throwTCError $ BadRecordField fld t_tp
  typeInfer (Sort s _) = liftTCM scSort (sortOf s)
  typeInfer (NatLit _) = liftTCM scNatType
  typeInfer (ArrayValue (SCTypedTerm tp tp_tp _) vs) =
    do n <- liftTCM scNat (fromIntegral (V.length vs))
       _ <- ensureSort tp_tp -- TODO: do we care about the level?
       tp' <- typeCheckWHNF tp
       forM_ vs $ \v_elem -> checkSubtype v_elem tp'
       liftTCM scVecType n tp'
  typeInfer (StringLit{}) = liftTCM scStringType

  typeInferComplete ftf =
    SCTypedTerm
    <$> liftTCM scFlatTermF (fmap typedVal ftf)
    <*> withErrorSCTypedTermF (FTermF ftf) (typeInfer ftf)
    <*> askCtx'

-- | Check that @fun_tp=Pi x a b@ and that @arg@ has type @a@, and return the
-- result of substituting @arg@ for @x@ in the result type @b@, i.e.,
-- @[arg/x]b@. This substitution could create redexes, so we call the
-- evaluator. If @fun_tp@ is not a pi type, raise the supplied error.
applyPiTyped :: TCError -> Term -> SCTypedTerm -> TCM Term
applyPiTyped err fun_tp arg =
  ensurePiType err fun_tp >>= \(_,arg_tp,ret_tp) ->
  do checkSubtype arg arg_tp
     liftTCM instantiateVar 0 (typedVal arg) ret_tp >>= typeCheckWHNF

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
ensurePiType :: TCError -> Term -> TCM (LocalName, Term, Term)
ensurePiType err tp = ensureRecognizer asPi err tp

-- | Reduce a type to WHNF (using 'scWhnf'), also adding in some conversions for
-- operations on Nat literals that are useful in type-checking
typeCheckWHNF :: Term -> TCM Term
typeCheckWHNF = liftTCM scTypeCheckWHNF

-- | The 'IO' version of 'typeCheckWHNF'
scTypeCheckWHNF :: SharedContext -> Term -> IO Term
scTypeCheckWHNF sc t =
  do (_, t') <- rewriteSharedTerm sc (addConvs natConversions emptySimpset :: Simpset ()) t
     scWhnf sc t'

-- | Check that one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s, and that they are both
-- already in WHNF
checkSubtype :: SCTypedTerm -> Term -> TCM ()
checkSubtype arg req_tp =
  do ok <- isSubtype (typedType arg) req_tp
     if ok then return () else throwTCError $ SubtypeFailure arg req_tp

-- | Check if one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s, and that they are both
-- already in WHNF
isSubtype :: Term -> Term -> TCM Bool
isSubtype (unwrapTermF -> Pi x1 a1 b1) (unwrapTermF -> Pi _ a2 b2) =
    (&&) <$> areConvertible a1 a2 <*> withVar x1 a1 (isSubtype b1 b2)
isSubtype (asSort -> Just s1) (asSort -> Just s2) | s1 <= s2 = return True
isSubtype t1' t2' = areConvertible t1' t2'

-- | Check if two terms are "convertible for type-checking", meaning that they
-- are convertible up to 'natConversions'
areConvertible :: Term -> Term -> TCM Bool
areConvertible t1 t2 = liftTCM scConvertibleEval scTypeCheckWHNF True t1 t2


inferRecursorType ::
  DataType      {- ^ data type -} ->
  [SCTypedTerm] {- ^ data type parameters -} ->
  Int           {- ^ number of indexes -} ->
  SCTypedTerm   {- ^ elimination motive -} ->
  SCTypedTerm   {- ^ type of the recursor as a function -} ->
  TCM Sort
inferRecursorType dt params nixs motive ty =
  do let d = dtName dt
     let mk_err str =
           MalformedRecursor
           (Unshared $ fmap typedVal $ FTermF $
             Recursor (CompiledRecursor d params nixs motive [] ty))
            str

     -- Check that the params have the correct types by making sure
     -- they correspond to the input types of dt
     unless (length params == length (dtParams dt)) $
       throwTCError $ mk_err "Incorrect number of parameters"
     _ <- foldM (applyPiTyped (mk_err "Incorrect data type signature"))
                (dtType dt) params

     -- Get the type of p_ret and make sure that it is of the form
     --
     -- (ix1::Ix1) -> .. -> (ixn::Ixn) -> d params ixs -> s
     --
     -- for some allowed sort s, where the Ix are the indices of of dt
     motive_srt <-
       case asPiList (typedType motive) of
         (_, (asSort -> Just s)) -> return s
         _ -> throwTCError $ mk_err "Motive function should return a sort"
     motive_req <-
       liftTCM scRecursorRetTypeType dt (map typedVal params) motive_srt
     -- Technically this is an equality test, not a subtype test, but we
     -- use the precise sort used in the motive, so they are the same, and
     -- checkSubtype is handy...
     checkSubtype motive motive_req
     unless (allowedElimSort dt motive_srt)  $
       throwTCError $ mk_err "Disallowed propositional elimination"

     return motive_srt


compileRecursor ::
  DataType ->
  [SCTypedTerm] {- ^ datatype parameters -} ->
  SCTypedTerm   {- ^ elimination motive -} ->
  TCM (CompiledRecursor SCTypedTerm)
compileRecursor dt params motive =
  do let d = dtName dt
     let nixs = length (dtIndices dt)
     let ctorOrder = map ctorName (dtCtors dt)

     -- Compute the types of the elimination functions [(Name, Term)]
     elims_tps <-
       liftTCM scRecursorElimTypes d (map typedVal params) (typedVal motive)

     ty1 <- liftTCM scRecursorAppType dt (map typedVal params) (typedVal motive)
     ty2 <- liftTCM scFunAll (map snd elims_tps) ty1
     ty <- typeInferComplete ty2
     let crec = CompiledRecursor d params nixs motive ctorOrder ty

     -- Check that the parameters and motive are correct for the given datatype
     _s <- inferRecursorType dt params nixs motive ty

     return crec


inferRecursor ::
  CompiledRecursor SCTypedTerm ->
  TCM Term
inferRecursor r =
  pure (typedVal (recursorType r))

-- | Compute the type of an 'SCTypedTerm'.
scTypeOfTypedTerm :: SharedContext -> SCTypedTerm -> IO SCTypedTerm
scTypeOfTypedTerm sc (SCTypedTerm _tm tp ctx) =
  do tp_tp <- scTypeOf' sc ctx tp
     -- Shrink de Bruijn context if possible
     let ctx' = take (bitSetBound (looseVars tp_tp)) ctx
     pure (SCTypedTerm tp tp_tp ctx')

-- | Reduce an 'SCTypedTerm' to WHNF (see also 'scTypeCheckWHNF').
scTypedTermWHNF :: SharedContext -> SCTypedTerm -> IO SCTypedTerm
scTypedTermWHNF sc (SCTypedTerm tm tp ctx) =
  do tm' <- scTypeCheckWHNF sc tm
     pure (SCTypedTerm tm' tp ctx)

scGlobalTypedTerm :: SharedContext -> Ident -> IO SCTypedTerm
scGlobalTypedTerm sc ident =
  do tm <- scGlobalDef sc ident
     tp <- scTypeOfIdent sc ident
     pure (SCTypedTerm tm tp [])
