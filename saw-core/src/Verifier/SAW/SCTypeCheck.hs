{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Module      : Verifier.SAW.SCTypeCheck
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module Verifier.SAW.SCTypeCheck
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
  , TypedTerm(..)
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
import Control.Monad.Except
import Control.Monad.State.Strict
import Control.Monad.Reader

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (Traversable(..))
#endif
import qualified Data.Vector as V
import Prelude hiding (mapM, maximum)

import Verifier.SAW.Conversion (natConversions)
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST
import Verifier.SAW.Module
import Verifier.SAW.Position

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
type TCM a =
  ReaderT (SharedContext, Maybe ModuleName, [(LocalName, Term)])
  (StateT TCState (ExceptT TCError IO)) a

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
  | NotFuncTypeInApp TypedTerm TypedTerm
  | NotTupleType Term
  | BadTupleIndex Int Term
  | NotStringLit Term
  | NotRecordType TypedTerm
  | BadRecordField FieldName Term
  | DanglingVar Int
  | UnboundName Text
  | SubtypeFailure TypedTerm Term
  | EmptyVectorLit
  | NoSuchDataType Ident
  | NoSuchCtor Ident
  | NotFullyAppliedRec (PrimName Term)
  | BadParamsOrArgsLength Bool (PrimName Term) [Term] [Term]
  | BadConstType NameInfo Term Term
  | MalformedRecursor Term String
  | DeclError Text String
  | ErrorPos Pos TCError
  | ErrorCtx LocalName Term TCError
  | ExpectedRecursor TypedTerm


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
  helper (NotRecordType (TypedTerm trm tp)) =
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
  helper (NotFullyAppliedRec i) =
      ppWithPos [ return ("Recursor not fully applied: " ++ show i) ]
  helper (BadParamsOrArgsLength is_dt ident params args) =
      ppWithPos
      [ return ("Wrong number of parameters or arguments to "
                ++ (if is_dt then "datatype" else "constructor") ++ ": "),
        ishow (Unshared $ FTermF $
               (if is_dt then DataTypeApp else CtorApp) ident params args)
      ]
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
  helper (ExpectedRecursor ttm) =
    ppWithPos [ return "Expected recursor value", ishow (typedVal ttm), ishow (typedType ttm)]

  ishow :: Term -> PPErrM String
  ishow tm =
    -- return $ show tm
    (\(ctx,_) -> "  " ++ scPrettyTermInCtx defaultPPOpts ctx tm) <$> ask

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
                            Maybe ModuleName -> a -> IO TypedTerm
scTypeCheckCompleteError sc mnm t0 =
  either (fail . unlines . prettyTCError) return =<<
  scTypeCheckComplete sc mnm t0

-- | Infer the type of an @a@ and complete it to a term, ensuring in the
-- process that the entire term is well-formed and that all internal type
-- annotations are correct. Types are evaluated to WHNF as necessary, and the
-- returned type is in WHNF, though the returned term may not be.
scTypeCheckComplete :: TypeInfer a => SharedContext -> Maybe ModuleName ->
                       a -> IO (Either TCError TypedTerm)
scTypeCheckComplete sc mnm = scTypeCheckCompleteInCtx sc mnm []

-- | Like 'scTypeCheckComplete', but type-check the term relative to a typing
-- context, which assigns types to free variables in the term
scTypeCheckCompleteInCtx :: TypeInfer a => SharedContext ->
                            Maybe ModuleName -> [(LocalName, Term)] -> a ->
                            IO (Either TCError TypedTerm)
scTypeCheckCompleteInCtx sc mnm ctx t0 =
  runTCM (typeInferComplete t0) sc mnm ctx

-- | Check that one type is a subtype of another using 'checkSubtype', calling
-- 'fail' on failure
scCheckSubtype :: SharedContext -> Maybe ModuleName ->
                  TypedTerm -> Term -> IO ()
scCheckSubtype sc mnm arg req_tp =
  either (fail . unlines . prettyTCError) return =<<
  runTCM (checkSubtype arg req_tp) sc mnm []

-- | A pair of a 'Term' and its type
data TypedTerm = TypedTerm { typedVal :: Term, typedType :: Term }

-- | The class of things that we can infer types of. The 'typeInfer' method
-- returns the most general (with respect to subtyping) type of its input.
class TypeInfer a where
  -- | Infer the type of an @a@
  typeInfer :: a -> TCM Term
  -- | Infer the type of an @a@ and complete it to a 'Term'
  typeInferComplete :: a -> TCM TypedTerm

-- | Infer the type of an @a@ and complete it to a 'Term', and then evaluate the
-- resulting term to WHNF
typeInferCompleteWHNF :: TypeInfer a => a -> TCM TypedTerm
typeInferCompleteWHNF a =
  do TypedTerm a_trm a_tp <- typeInferComplete a
     a_whnf <- typeCheckWHNF a_trm
     return $ TypedTerm a_whnf a_tp


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
  typeInfer (Unshared tf) = typeInfer tf
  typeInfer (STApp{ stAppIndex = i, stAppTermF = tf}) =
    do table <- get
       case Map.lookup i table of
         Just x  -> return x
         Nothing ->
           do x <- typeInfer tf
              x' <- typeCheckWHNF x
              modify (Map.insert i x')
              return x'
  typeInferComplete trm = TypedTerm trm <$> typeInfer trm

-- Type inference for TermF Term dispatches to that for TermF TypedTerm by
-- calling inference on all the sub-components and extending the context inside
-- of the binding forms
instance TypeInfer (TermF Term) where
  typeInfer (Lambda x a rhs) =
    do a_tptrm <- typeInferCompleteWHNF a
       -- NOTE: before adding a type to the context, we want to be sure it is in
       -- WHNF, so we don't have to normalize each time we look up a var type
       rhs_tptrm <- withVar x (typedVal a_tptrm) $ typeInferComplete rhs
       typeInfer (Lambda x a_tptrm rhs_tptrm)
  typeInfer (Pi x a rhs) =
    do a_tptrm <- typeInferCompleteWHNF a
       -- NOTE: before adding a type to the context, we want to be sure it is in
       -- WHNF, so we don't have to normalize each time we look up a var type
       rhs_tptrm <- withVar x (typedVal a_tptrm) $ typeInferComplete rhs
       typeInfer (Pi x a_tptrm rhs_tptrm)
  typeInfer t = typeInfer =<< mapM typeInferComplete t
  typeInferComplete tf =
    TypedTerm <$> liftTCM scTermF tf <*> typeInfer tf

-- Type inference for FlatTermF Term dispatches to that for FlatTermF TypedTerm
instance TypeInfer (FlatTermF Term) where
  typeInfer t = typeInfer =<< mapM typeInferComplete t
  typeInferComplete ftf =
    TypedTerm <$> liftTCM scFlatTermF ftf <*> typeInfer ftf


-- Type inference for TermF TypedTerm is the main workhorse. Intuitively, this
-- represents the case where each immediate subterm of a term is labeled with
-- its (most general) type.
instance TypeInfer (TermF TypedTerm) where
  typeInfer (FTermF ftf) = typeInfer ftf
  typeInfer (App x@(TypedTerm _ x_tp) y) =
    applyPiTyped (NotFuncTypeInApp x y) x_tp y
  typeInfer (Lambda x (TypedTerm a a_tp) (TypedTerm _ b)) =
    void (ensureSort a_tp) >> liftTCM scTermF (Pi x a b)
  typeInfer (Pi _ (TypedTerm _ a_tp) (TypedTerm _ b_tp)) =
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
  typeInfer (Constant (EC _ n (TypedTerm req_tp req_tp_sort)) (TypedTerm _ tp)) =
    do void (ensureSort req_tp_sort)
       -- NOTE: we do the subtype check here, rather than call checkSubtype, so
       -- that we can throw the custom BadConstType error on failure
       ok <- isSubtype tp req_tp
       if ok then return tp else
         throwTCError $ BadConstType n tp req_tp
  typeInferComplete tf =
    TypedTerm <$> liftTCM scTermF (fmap typedVal tf) <*> typeInfer tf


-- Type inference for FlatTermF TypedTerm is the main workhorse for flat
-- terms. Intuitively, this represents the case where each immediate subterm of
-- a term has already been labeled with its (most general) type.
instance TypeInfer (FlatTermF TypedTerm) where
  typeInfer (Primitive ec) =
    typeCheckWHNF $ typedVal $ primType ec
  typeInfer UnitValue = liftTCM scUnitType
  typeInfer UnitType = liftTCM scSort (mkSort 0)
  typeInfer (PairValue (TypedTerm _ tx) (TypedTerm _ ty)) =
    liftTCM scPairType tx ty
  typeInfer (PairType (TypedTerm _ tx) (TypedTerm _ ty)) =
    do sx <- ensureSort tx
       sy <- ensureSort ty
       liftTCM scSort (max sx sy)
  typeInfer (PairLeft (TypedTerm _ tp)) =
    case asPairType tp of
      Just (t1, _) -> typeCheckWHNF t1
      _ -> throwTCError (NotTupleType tp)
  typeInfer (PairRight (TypedTerm _ tp)) =
    case asPairType tp of
      Just (_, t2) -> typeCheckWHNF t2
      _ -> throwTCError (NotTupleType tp)

  typeInfer (DataTypeApp d params args) =
    -- Look up the DataType structure, check the length of the params and args,
    -- and then apply the cached Pi type of dt to params and args
    do dt <- liftTCM scRequireDataType (primName d)
       if length params == length (dtParams dt) &&
          length args == length (dtIndices dt) then return () else
         throwTCError $
         BadParamsOrArgsLength True (fmap typedVal d) (map typedVal params) (map typedVal args)

       -- NOTE: we assume dtType is already well-typed and in WHNF
       -- _ <- inferSort t
       -- t' <- typeCheckWHNF t
       foldM (applyPiTyped (error "TODO")) (dtType dt) (params ++ args)

  typeInfer (CtorApp c params args) =
    -- Look up the Ctor structure, check the length of the params and args, and
    -- then apply the cached Pi type of ctor to params and args
    do ctor <- liftTCM scRequireCtor (primName c)
       if length params == ctorNumParams ctor &&
          length args == ctorNumArgs ctor then return () else
         throwTCError $
         BadParamsOrArgsLength False (fmap typedVal c) (map typedVal params) (map typedVal args)
       -- NOTE: we assume ctorType is already well-typed and in WHNF
       foldM (applyPiTyped (error "TODO")) (ctorType ctor) (params ++ args)

  typeInfer (RecursorType d ps motive mty) =
    do s <- inferRecursorType d ps motive mty
       liftTCM scSort s

  typeInfer (Recursor rec) =
    inferRecursor rec

  typeInfer (RecursorApp rec ixs arg) =
    inferRecursorApp rec ixs arg

  typeInfer (RecordType elems) =
    -- NOTE: record types are always predicative, i.e., non-Propositional, so we
    -- ensure below that we return at least sort 0
    do sorts <- mapM (ensureSort . typedType . snd) elems
       liftTCM scSort (maxSort $ mkSort 0 : sorts)
  typeInfer (RecordValue elems) =
    liftTCM scFlatTermF $ RecordType $
    map (\(f,TypedTerm _ tp) -> (f,tp)) elems
  typeInfer (RecordProj t@(TypedTerm _ t_tp) fld) =
    case asRecordType t_tp of
      Just (Map.lookup fld -> Just tp) -> return tp
      Just _ -> throwTCError $ BadRecordField fld t_tp
      Nothing -> throwTCError $ NotRecordType t
  typeInfer (Sort s) = liftTCM scSort (sortOf s)
  typeInfer (NatLit _) = liftTCM scNatType
  typeInfer (ArrayValue (TypedTerm tp tp_tp) vs) =
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
    TypedTerm <$> liftTCM scFlatTermF (fmap typedVal ftf) <*> typeInfer ftf

-- | Check that @fun_tp=Pi x a b@ and that @arg@ has type @a@, and return the
-- result of substituting @arg@ for @x@ in the result type @b@, i.e.,
-- @[arg/x]b@. This substitution could create redexes, so we call the
-- evaluator. If @fun_tp@ is not a pi type, raise the supplied error.
applyPiTyped :: TCError -> Term -> TypedTerm -> TCM Term
applyPiTyped err fun_tp arg =
  case asPi fun_tp of
    Just (_, arg_tp, ret_tp) -> do
      -- _ <- ensureSort aty -- NOTE: we assume tx is well-formed and WHNF
      -- aty' <- scTypeCheckWHNF aty
      checkSubtype arg arg_tp
      liftTCM instantiateVar 0 (typedVal arg) ret_tp >>= typeCheckWHNF
    _ -> throwTCError err

-- | Ensure that a 'Term' is a sort, and return that sort
ensureSort :: Term -> TCM Sort
ensureSort (asSort -> Just s) = return s
ensureSort tp = throwTCError $ NotSort tp

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
checkSubtype :: TypedTerm -> Term -> TCM ()
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
  PrimName TypedTerm {- ^ data type name -} ->
  [TypedTerm] {- ^ data type parameters -} ->
  TypedTerm   {- ^ elimination motive -} ->
  TypedTerm   {- ^ type of the elimination motive -} ->
  TCM Sort
inferRecursorType d params motive motiveTy =
  do dt <- liftTCM scRequireDataType (primName d)

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
  [TypedTerm] {- ^ datatype parameters -} ->
  TypedTerm   {- ^ elimination motive -} ->
  [TypedTerm] {- ^ constructor eliminators -} ->
  TCM (CompiledRecursor TypedTerm)
compileRecursor dt params motive cs_fs =
  do motiveTy <- typeInferComplete (typedType motive)
     cs_fs' <- forM cs_fs (\e -> do ety <- typeInferComplete (typedType e)
                                    pure (e,ety))
     d <- traverse typeInferComplete (dtPrimName dt)
     let ctorVarIxs = map ctorVarIndex (dtCtors dt)
     ctorOrder <- traverse (traverse typeInferComplete) (map ctorPrimName (dtCtors dt))
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
       liftTCM scRecursorElimTypes (fmap typedVal d) (map typedVal params) (typedVal motive)

     forM_ elims_tps $ \(c,req_tp) ->
       case Map.lookup (primVarIndex c) elims of
         Nothing ->
           throwTCError $ mk_err ("Missing constructor: " ++ show c)
         Just (f,_fty) -> checkSubtype f req_tp

     return rec


inferRecursor ::
  CompiledRecursor TypedTerm ->
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
  TypedTerm   {- ^ recursor term -} ->
  [TypedTerm] {- ^ data type indices -} ->
  TypedTerm   {- ^ recursor argument -} ->
  TCM Term
inferRecursorApp rec ixs arg =
  do recty <- typeCheckWHNF (typedType rec)
     case asRecursorType recty of
       Nothing -> throwTCError (ExpectedRecursor rec)
       Just (_d, _ps, motive, motiveTy) -> do

         -- Apply the indices to the type of the motive
         -- to check the types of the `ixs` and `arg`, and
         -- ensure that the result is fully applied

         _s <- ensureSort =<<
                  foldM (applyPiTyped (error "Internal type-checking error: unexpected non-pi type!"))
                     motiveTy (ixs ++ [arg])
    
         -- return the type (p_ret ixs arg)
         liftTCM scTypeCheckWHNF =<<
           liftTCM scApplyAll motive (map typedVal (ixs ++ [arg]))
