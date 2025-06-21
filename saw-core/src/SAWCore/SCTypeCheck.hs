{-# LANGUAGE CPP #-}
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
  , askModName
  , withVar
  , withCtx
  , atPos
  , LiftTCM(..)
  , SCTypedTerm(..)
  , TypeInfer(..)
  , typeCheckWHNF
  , typeInferCompleteWHNF
  , TypeInferCtx(..)
  , typeInferCompleteInCtx
  , checkSubtype
  , ensureSort
  , applyPiTyped
  , compileRecursor
  ) where

import Control.Applicative
import Control.Monad (foldM, forM, forM_, mapM, unless, void)
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), Reader, ReaderT(..), runReader)
import Control.Monad.State.Strict (MonadState(..), StateT, evalStateT, modify)

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (Traversable(..))
#endif
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
  , ResolvedName(..)
  )
import SAWCore.Name
import SAWCore.Recognizer
import SAWCore.Rewriter
import SAWCore.SharedTerm
import SAWCore.Position
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (scPrettyTermInCtx)

-- | The state for a type-checking computation = a memoization table
type TCState = Map TermIndex Term

-- | The monad for type checking and inference, which:
--
-- * Maintains a 'SharedContext', the name of the current module, and a variable
-- context, where the latter assigns types to the deBruijn indices in scope;
--
-- * Memoizes the most general type inferred for each expression; AND
--
-- * Can throw 'TCError's
type TCM =
  ReaderT (SharedContext, Maybe ModuleName, [(LocalName, Term)])
  (StateT TCState (ExceptT TCError IO))

-- | Run a type-checking computation in a given context, starting from the empty
-- memoization table
runTCM ::
  TCM a -> SharedContext -> Maybe ModuleName -> [(LocalName, Term)] ->
  IO (Either TCError a)
runTCM m sc mnm ctx =
  runExceptT $ evalStateT (runReaderT m (sc, mnm, ctx)) Map.empty

-- | Read the current typing context
askCtx :: TCM [(LocalName, Term)]
askCtx = (\(_,_,ctx) -> ctx) <$> ask

-- | Read the current module name
askModName :: TCM (Maybe ModuleName)
askModName = (\(_,mnm,_) -> mnm) <$> ask

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given type. This throws away the memoization table while
-- running the sub-computation, as memoization tables are tied to specific sets
-- of bindings.
--
-- NOTE: the type given for the variable should be in WHNF, so that we do not
-- have to normalize the types of variables each time we see them.
withVar :: LocalName -> Term -> TCM a -> TCM a
withVar x tp m =
  flip catchError (throwError . ErrorCtx x tp) $
  do saved_table <- get
     put Map.empty
     a <- local (\(sc,mnm,ctx) -> (sc, mnm, (x,tp):ctx)) m
     put saved_table
     return a

-- | Run a type-checking computation in a typing context extended by a list of
-- variables and their types. See 'withVar'.
withCtx :: [(LocalName, Term)] -> TCM a -> TCM a
withCtx = flip (foldr (\(x,tp) -> withVar x tp))

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
atPos :: Pos -> TCM a -> TCM a
atPos p m = catchError m (throwError . ErrorPos p)

-- | Typeclass for lifting 'IO' computations that take a 'SharedContext' to
-- 'TCM' computations
class LiftTCM a where
  type TCMLifted a
  liftTCM :: (SharedContext -> a) -> TCMLifted a

instance LiftTCM (IO a) where
  type TCMLifted (IO a) = TCM a
  liftTCM f =
    do sc <- (\(sc,_,_) -> sc) <$> ask
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
  | NotStringLit Term
  | NotRecordType SCTypedTerm
  | BadRecordField FieldName Term
  | DanglingVar Int
  | UnboundName Text
  | SubtypeFailure SCTypedTerm Term
  | EmptyVectorLit
  | NoSuchDataType NameInfo
  | NoSuchCtor NameInfo
  | NoSuchConstant NameInfo
  | NotFullyAppliedRec (ExtCns Term)
  | BadRecursorApp Term [Term] Term
  | BadConstType NameInfo Term Term
  | MalformedRecursor Term String
  | DeclError Text String
  | ErrorPos Pos TCError
  | ErrorCtx LocalName Term TCError
  | ErrorTerm Term TCError
  | ExpectedRecursor SCTypedTerm


-- | Throw a type-checking error
throwTCError :: TCError -> TCM a
throwTCError = throwError

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
  helper (NotStringLit trm) =
      ppWithPos [ return "Record selector is not a string literal", ishow trm ]
  helper (NotRecordType (SCTypedTerm trm tp)) =
      ppWithPos [ return "Record field projection with non-record type"
                , ishow tp
                , return "In term:"
                , ishow trm ]
  helper (BadRecordField n ty) =
      ppWithPos [ return ("Bad record field (" ++ show n ++ ") for type")
                , ishow ty ]
  helper (BadRecursorApp r ixs arg) =
      ppWithPos [ return "Type mismatch in recursor application"
                , ishow (Unshared $ FTermF $ RecursorApp r ixs arg)
                ]
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
  helper (BadConstType n rty ty) =
    ppWithPos [ return ("Type of constant " ++ show n), ishow rty
              , return "doesn't match declared type", ishow ty ]
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
    info <- ppWithPos [ return ("While typechecking term: ")
                      , ishow tm ]
    cont <- helper err
    return (info ++ cont)
  helper (ExpectedRecursor ttm) =
    ppWithPos [ return "Expected recursor value", ishow (typedVal ttm), ishow (typedType ttm)]

  ishow :: Term -> PPErrM String
  ishow tm =
    -- return $ show tm
    (\(ctx,_) -> "  " ++ scPrettyTermInCtx PPS.defaultOpts ctx tm) <$> ask

instance Show TCError where
  show = unlines . prettyTCError

-- | Infer the type of a term using 'scTypeCheck', calling 'fail' on failure
scTypeCheckError :: TypeInfer a => SharedContext -> a -> IO Term
scTypeCheckError sc t0 =
  either (fail . unlines . prettyTCError) return =<< scTypeCheck sc Nothing t0

-- | Infer the type of a 'Term', ensuring in the process that the entire term is
-- well-formed and that all internal type annotations are correct. Types are
-- evaluated to WHNF as necessary, and the returned type is in WHNF.
scTypeCheck :: TypeInfer a => SharedContext -> Maybe ModuleName -> a ->
               IO (Either TCError Term)
scTypeCheck sc mnm = scTypeCheckInCtx sc mnm []

-- | Like 'scTypeCheck', but type-check the term relative to a typing context,
-- which assigns types to free variables in the term
scTypeCheckInCtx ::
  TypeInfer a => SharedContext -> Maybe ModuleName ->
  [(LocalName, Term)] -> a -> IO (Either TCError Term)
scTypeCheckInCtx sc mnm ctx t0 = runTCM (typeInfer t0) sc mnm ctx

-- | Infer the type of an @a@ and complete it to a term using
-- 'scTypeCheckComplete', calling 'fail' on failure
scTypeCheckCompleteError :: TypeInfer a => SharedContext ->
                            Maybe ModuleName -> a -> IO SCTypedTerm
scTypeCheckCompleteError sc mnm t0 =
  either (fail . unlines . prettyTCError) return =<<
  scTypeCheckComplete sc mnm t0

-- | Infer the type of an @a@ and complete it to a term, ensuring in the
-- process that the entire term is well-formed and that all internal type
-- annotations are correct. Types are evaluated to WHNF as necessary, and the
-- returned type is in WHNF, though the returned term may not be.
scTypeCheckComplete :: TypeInfer a => SharedContext -> Maybe ModuleName ->
                       a -> IO (Either TCError SCTypedTerm)
scTypeCheckComplete sc mnm = scTypeCheckCompleteInCtx sc mnm []

-- | Like 'scTypeCheckComplete', but type-check the term relative to a typing
-- context, which assigns types to free variables in the term
scTypeCheckCompleteInCtx :: TypeInfer a => SharedContext ->
                            Maybe ModuleName -> [(LocalName, Term)] -> a ->
                            IO (Either TCError SCTypedTerm)
scTypeCheckCompleteInCtx sc mnm ctx t0 =
  runTCM (typeInferComplete t0) sc mnm ctx

-- | Check that one type is a subtype of another using 'checkSubtype', calling
-- 'fail' on failure
scCheckSubtype :: SharedContext -> Maybe ModuleName ->
                  SCTypedTerm -> Term -> IO ()
scCheckSubtype sc mnm arg req_tp =
  either (fail . unlines . prettyTCError) return =<<
  runTCM (checkSubtype arg req_tp) sc mnm []

-- | A pair of a 'Term' and its type
data SCTypedTerm = SCTypedTerm { typedVal :: Term, typedType :: Term }

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
  do SCTypedTerm a_trm a_tp <- typeInferComplete a
     a_whnf <- typeCheckWHNF a_trm
     return $ SCTypedTerm a_whnf a_tp


-- | Perform type inference on a context, i.e., a list of variable names and
-- their associated types. The type @var@ gives the type of variable names,
-- while @a@ is the type of types. This will give us 'Term's for each type, as
-- well as their 'Sort's, since the type of any type is a 'Sort'.
class TypeInferCtx var a where
  typeInferCompleteCtx :: [(var,a)] -> TCM [(LocalName, Term, Sort)]

instance TypeInfer a => TypeInferCtx LocalName a where
  typeInferCompleteCtx [] = return []
  typeInferCompleteCtx ((x,tp):ctx) =
    do typed_tp <- typeInferComplete tp
       s <- ensureSort (typedType typed_tp)
       ((x,typedVal typed_tp,s):) <$>
         withVar x (typedVal typed_tp) (typeInferCompleteCtx ctx)

-- | Perform type inference on a context via 'typeInferCompleteCtx', and then
-- run a computation in that context via 'withCtx', also passing in that context
-- to the computation
typeInferCompleteInCtx ::
  TypeInferCtx var tp => [(var, tp)] ->
  ([(LocalName, Term, Sort)] -> TCM a) -> TCM a
typeInferCompleteInCtx ctx f =
  do typed_ctx <- typeInferCompleteCtx ctx
     withCtx (map (\(x,tp,_) -> (x,tp)) typed_ctx) (f typed_ctx)


-- Type inference for Term dispatches to type inference on TermF Term, but uses
-- memoization to avoid repeated work
instance TypeInfer Term where
  typeInfer t@(Unshared tf) = withErrorTerm t $ typeInfer tf
  typeInfer t@(STApp{ stAppIndex = i, stAppTermF = tf}) =
    do table <- get
       case Map.lookup i table of
         Just x  -> return x
         Nothing ->
           do x  <- withErrorTerm t $ typeInfer tf
              x' <- typeCheckWHNF x
              modify (Map.insert i x')
              return x'
  typeInferComplete trm = SCTypedTerm trm <$> withErrorTerm trm (typeInfer trm)

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
       let a_tptrm = SCTypedTerm a (typedType a_whnf)
       typeInfer (Lambda x a_tptrm rhs_tptrm)
  typeInfer (Pi x a rhs) =
    do a_whnf <- typeInferCompleteWHNF a
       -- NOTE: before adding a type to the context, we want to be sure it is in
       -- WHNF, so we don't have to normalize each time we look up a var type,
       -- but we want to leave the non-normalized value of a in the returned
       -- term, so we create a_typed with the type of a_whnf but the value of a
       rhs_tptrm <- withVar x (typedVal a_whnf) $ typeInferComplete rhs
       let a_tptrm = SCTypedTerm a (typedType a_whnf)
       typeInfer (Pi x a_tptrm rhs_tptrm)
  typeInfer (Constant nm) = typeInferConstant nm
  typeInfer t = typeInfer =<< mapM typeInferComplete t
  typeInferComplete tf =
    SCTypedTerm <$> liftTCM scTermF tf <*> withErrorTermF tf (typeInfer tf)

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
  typeInfer (ExtCns ec) = return $ ecType ec
  typeInfer t = typeInfer =<< mapM typeInferComplete t
  typeInferComplete ftf =
    SCTypedTerm <$> liftTCM scFlatTermF ftf
              <*> withErrorTermF (FTermF ftf) (typeInfer ftf)


-- Type inference for TermF SCTypedTerm is the main workhorse. Intuitively, this
-- represents the case where each immediate subterm of a term is labeled with
-- its (most general) type.
instance TypeInfer (TermF SCTypedTerm) where
  typeInfer (FTermF ftf) = typeInfer ftf
  typeInfer (App x@(SCTypedTerm _ x_tp) y) =
    applyPiTyped (NotFuncTypeInApp x y) x_tp y
  typeInfer (Lambda x (SCTypedTerm a a_tp) (SCTypedTerm _ b)) =
    void (ensureSort a_tp) >> liftTCM scTermF (Pi x a b)
  typeInfer (Pi _ (SCTypedTerm _ a_tp) (SCTypedTerm _ b_tp)) =
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

  typeInferComplete tf =
    SCTypedTerm <$> liftTCM scTermF (fmap typedVal tf)
              <*> withErrorSCTypedTermF tf (typeInfer tf)


-- Type inference for FlatTermF SCTypedTerm is the main workhorse for flat
-- terms. Intuitively, this represents the case where each immediate subterm of
-- a term has already been labeled with its (most general) type.
instance TypeInfer (FlatTermF SCTypedTerm) where
  typeInfer UnitValue = liftTCM scUnitType
  typeInfer UnitType = liftTCM scSort (mkSort 0)
  typeInfer (PairValue (SCTypedTerm _ tx) (SCTypedTerm _ ty)) =
    liftTCM scPairType tx ty
  typeInfer (PairType (SCTypedTerm _ tx) (SCTypedTerm _ ty)) =
    do sx <- ensureSort tx
       sy <- ensureSort ty
       liftTCM scSort (max sx sy)
  typeInfer (PairLeft (SCTypedTerm _ tp)) =
    ensurePairType tp >>= \(t1,_) -> return t1
  typeInfer (PairRight (SCTypedTerm _ tp)) =
    ensurePairType tp >>= \(_,t2) -> return t2

  typeInfer (RecursorType d ps motive mty) =
    do s <- inferRecursorType d ps motive mty
       liftTCM scSort s

  typeInfer (Recursor rec) =
    inferRecursor rec

  typeInfer (RecursorApp r ixs arg) =
    inferRecursorApp r ixs arg

  typeInfer (RecordType elems) =
    -- NOTE: record types are always predicative, i.e., non-Propositional, so we
    -- ensure below that we return at least sort 0
    do sorts <- mapM (ensureSort . typedType . snd) elems
       liftTCM scSort (maxSort $ mkSort 0 : sorts)
  typeInfer (RecordValue elems) =
    liftTCM scFlatTermF $ RecordType $
    map (\(f,SCTypedTerm _ tp) -> (f,tp)) elems
  typeInfer (RecordProj t@(SCTypedTerm _ t_tp) fld) =
    ensureRecordType (NotRecordType t) t_tp >>= \case
    (Map.lookup fld -> Just tp) -> return tp
    _ -> throwTCError $ BadRecordField fld t_tp
  typeInfer (Sort s _) = liftTCM scSort (sortOf s)
  typeInfer (NatLit _) = liftTCM scNatType
  typeInfer (ArrayValue (SCTypedTerm tp tp_tp) vs) =
    do n <- liftTCM scNat (fromIntegral (V.length vs))
       _ <- ensureSort tp_tp -- TODO: do we care about the level?
       tp' <- typeCheckWHNF tp
       forM_ vs $ \v_elem -> checkSubtype v_elem tp'
       liftTCM scVecType n tp'
  typeInfer (StringLit{}) = liftTCM scStringType
  typeInfer (ExtCns ec) =
    -- FIXME: should we check that the type of ecType is a sort?
    typeCheckWHNF $ typedVal $ ecType ec

  typeInferComplete ftf =
    SCTypedTerm <$> liftTCM scFlatTermF (fmap typedVal ftf)
              <*> withErrorSCTypedTermF (FTermF ftf) (typeInfer ftf)

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
  Name           {- ^ data type name -} ->
  [SCTypedTerm] {- ^ data type parameters -} ->
  SCTypedTerm   {- ^ elimination motive -} ->
  SCTypedTerm   {- ^ type of the elimination motive -} ->
  TCM Sort
inferRecursorType d params motive motiveTy =
  do mm <- liftTCM scGetModuleMap
     dt <-
       case lookupVarIndexInMap (nameIndex d) mm of
         Just (ResolvedDataType dt) -> pure dt
         _ -> throwTCError $ NoSuchDataType (nameInfo d)

     let mk_err str =
           MalformedRecursor
           (Unshared $ fmap typedVal $ FTermF $
             Recursor (CompiledRecursor d params motive motiveTy mempty []))
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
  [SCTypedTerm] {- ^ constructor eliminators -} ->
  TCM (CompiledRecursor SCTypedTerm)
compileRecursor dt params motive cs_fs =
  do motiveTy <- typeInferComplete (typedType motive)
     cs_fs' <- forM cs_fs (\e -> do ety <- typeInferComplete (typedType e)
                                    pure (e,ety))
     let d = dtName dt
     let ctorVarIxs = map ctorVarIndex (dtCtors dt)
     let ctorOrder = map ctorName (dtCtors dt)
     let elims = Map.fromList (zip ctorVarIxs cs_fs')
     let rec = CompiledRecursor d params motive motiveTy elims ctorOrder
     let mk_err str =
           MalformedRecursor
            (Unshared $ fmap typedVal $ FTermF $ Recursor rec)
            str

     unless (length cs_fs == length (dtCtors dt)) $
       throwTCError $ mk_err "Extra constructors"

     -- Check that the parameters and motive are correct for the given datatype
     _s <- inferRecursorType d params motive motiveTy

     -- Check that the elimination functions each have the right types, and
     -- that we have exactly one for each constructor of dt
     elims_tps <-
       liftTCM scRecursorElimTypes d (map typedVal params) (typedVal motive)

     forM_ elims_tps $ \(c,req_tp) ->
       case Map.lookup (nameIndex c) elims of
         Nothing ->
           throwTCError $ mk_err ("Missing constructor: " ++ show c)
         Just (f,_fty) -> checkSubtype f req_tp

     return rec


inferRecursor ::
  CompiledRecursor SCTypedTerm ->
  TCM Term
inferRecursor rec =
  do let d      = recursorDataType rec
     let params = recursorParams rec
     let motive = recursorMotive rec
     let motiveTy = recursorMotiveTy rec

     -- return the type of this recursor
     liftTCM scFlatTermF $ fmap typedVal $
       RecursorType d params motive motiveTy

-- | Infer the type of a recursor application
inferRecursorApp ::
  SCTypedTerm   {- ^ recursor term -} ->
  [SCTypedTerm] {- ^ data type indices -} ->
  SCTypedTerm   {- ^ recursor argument -} ->
  TCM Term
inferRecursorApp r ixs arg =
  do recty <- typeCheckWHNF (typedType r)
     case asRecursorType recty of
       Nothing -> throwTCError (ExpectedRecursor r)
       Just (_d, _ps, motive, motiveTy) -> do

         -- Apply the indices to the type of the motive
         -- to check the types of the `ixs` and `arg`, and
         -- ensure that the result is fully applied

         let err = BadRecursorApp (typedVal r) (fmap typedVal ixs) (typedVal arg)
         _s <- ensureSort =<< foldM (applyPiTyped err) motiveTy (ixs ++ [arg])

         -- return the type (p_ret ixs arg)
         liftTCM scTypeCheckWHNF =<<
           liftTCM scApplyAll motive (map typedVal (ixs ++ [arg]))
