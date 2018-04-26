{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}

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
  , scTypeCheckWHNF
  , scSubtype
  , scConvertible
  , TCError(..)
  , tcErrorPath
  , prettyTCError
  , throwTCError
  ) where

import Control.Applicative
import Control.Lens
import Control.Monad.Trans.Except
import Control.Monad.State.Strict
import Control.Monad.Reader
import Control.Monad.IO.Class

import Data.Foldable (and)
import Data.Map (Map)
import qualified Data.Map as Map
#if !MIN_VERSION_base(4,8,0)
import Data.Traversable (Traversable(..))
#endif
import qualified Data.Vector as V
import Prelude hiding (mapM, maximum)

import Verifier.SAW.Conversion (natConversions)
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

-- | The state for a type-checking computation = a memoization table
type TCState = Map TermIndex Term

-- | The monad for type checking and inference, which:
--
-- * Maintains a variable context, giving types to the deBruijn indices in
-- scope, along with a 'SharedContext';
--
-- * Memoizes the most general type inferred for each expression; AND
--
-- * Can throw 'TCError's
type TCM a =
  ReaderT (SharedContext, [Term]) (StateT TCState (ExceptT TCError IO)) a

-- | Run a type-checking computation in a given context, starting from the empty
-- memoization table
runTCM :: TCM a -> SharedContext -> [Term] -> IO (Either TCError Term)
runTCM m sc ctx = runExceptT $ evalStateT (runReaderT m (sc, ctx)) Map.empty

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given type. This throws away the memoization table while
-- running the sub-computation, as memoization tables are tied to specific sets
-- of bindings.
inExtendedCtx :: Term -> TCM a -> TCM a
inExtendedCtx tp m =
  do saved_table <- get
     put Map.empty
     a <- local (\(sc,ctx) -> (sc, tp:ctx)) m
     put saved_table
     return a

-- | Lift a binary 'IO' function that takes in a 'SharedContext' to a unary
-- function to a 'TCM' computation
liftTCM1 :: (SharedContext -> a -> IO b) -> a -> TCM b
liftTCM1 f a = (fst <$> ask) >>= f a

-- | Lift a trinary 'IO' function that takes in a 'SharedContext' to a binary
-- function to a 'TCM' computation
liftTCM2 :: (SharedContext -> a -> b -> IO c) -> a -> b -> TCM c
liftTCM2 f a b = (fst <$> ask) >>= f a b

-- | Lift a quaternary (yes, that is the word) 'IO' function that takes in a
-- 'SharedContext' to a trinary function to a 'TCM' computation
liftTCM3 :: (SharedContext -> a -> b -> IO c) -> a -> b -> TCM c
liftTCM3 f a b = (fst <$> ask) >>= f a b

-- | Errors that can occur during type-checking
data TCError
  = NotSort Term
  | NotFuncType Term
  | ArgTypeMismatch Term Term
  | NotTupleType Term
  | BadTupleIndex Int Term
  | NotStringType Term
  | NotRecordType Term
  | BadRecordField FieldName Term
  | ArrayTypeMismatch Term Term
  | DanglingVar Int
  | DisallowedElimSort Term
  | BadParamsOrArgsLength Ident [Term] [Term]

-- | Throw a type-checking error
throwTCError :: TCError -> TCM a
throwTCError = lift . lift . throwE

-- | Pretty-print a type-checking error
prettyTCError :: TCError -> [String]
prettyTCError e =
  case e of
    NotSort ty ->
      [ "Not a sort" , ishow ty ]
    NotFuncType ty ->
      [ "Function application with non-function type" , ishow ty ]
    ArgTypeMismatch ety aty ->
      [ "Function argument type" , ishow aty
      , "doesn't match expected type" , ishow ety
      ]
    NotTupleType ty ->
      [ "Tuple field projection with non-tuple type" , ishow ty ]
    BadTupleIndex n ty ->
      [ "Bad tuple index (" ++ show n ++ ") for type"
      , ishow ty
      ]
    NotRecordType ty ->
      [ "Record field projection with non-record type" , ishow ty ]
    BadRecordField n ty ->
      [ "Bad record field (" ++ show n ++ ") for type"
      , ishow ty
      ]
    ArrayTypeMismatch ety aty ->
      [ "Array element type" , ishow aty
      , "doesn't match declared array element type" , ishow ety
      ]
    DanglingVar n ->
      [ "Dangling bound variable index: " ++ show n ]
    BadParamsOrArgsLength is_dt ident params args ->
      [ "Wrong number of parameters or arguments to "
        ++ (if is_dt then "datatype" else "constructor") ++ ": ",
        ishow (Unshared $
               (if is_dt then DataTypeApp else CtorApp) ident params args)
      ]
  where
    ishow = (' ':) . (' ':) . scPrettyTerm defaultPPOpts


-- | Infer the type of a term using 'scTypeCheck', calling 'fail' on failure
scTypeCheckError :: SharedContext -> Term -> IO Term
scTypeCheckError sc t0 =
  either (fail . unlines . prettyTCError) return =<< scTypeCheck sc t0

-- | Infer the type of a 'Term', ensuring in the process that the entire term is
-- well-formed and that all internal type annotations are correct. Types are
-- evaluated to WHNF as necessary, and the returned type is in WHNF.
scTypeCheck :: SharedContext -> Term -> IO (Either TCError Term)
scTypeCheck sc = scTypeCheckInCtx sc []

-- | Like 'scTypeCheck', but type-check the term relative to a typing context,
-- which assigns types to free variables in the term
scTypeCheckInCtx :: SharedContext -> [Term] -> Term -> IO (Either TCError Term)
scTypeCheckInCtx sc ctx t0 = runTCM (inferTerm t0) sc ctx

-- | A pair of a 'Term' and its type
data TypedTerm = TypedTerm { typedVal :: Term, typedType :: Term }

-- | The class of things that we can infer types of. The 'typeInfer' method
-- returns the most general (with respect to subtyping) type of its input.
class TypeInfer a where
  typeInfer :: a -> TCM Term

typeInferAndBuild :: TermF TypedTerm -> TCM TypedTerm
typeInferAndBuild tf =
  TypedTerm <$> liftTCM1 scTermF (fmap typedVal tf) <*> typeInfer tf

typeInferAndId :: Term -> TCM TypedTerm
typeInferAndId t = TypedTerm t <$> typeInfer t

-- Type inference for Term dispatches to type inference on TermF Term, but uses
-- memoization to avoid repeated work
instance TypeInfer Term where
  typeInfer (Unshared tf) = typeInfer tf
  typeInfer (STApp{ stAppIndex = i, stAppTermF = tf}) =
    do table <- get
       case Map.lookup i table of
         Just x  -> return x
         Nothing ->
           do x <- inferTermF tf
              x' <- typeCheckWHNF x
              modify (Map.insert i x')
              return x'

-- Type inference for TermF Term dispatches to that for TermF TypedTerm by
-- calling inference on all the sub-components and extending the context inside
-- of the binding forms
instance TypeInfer (TermF Term) where
  typeInfer (Lam x a rhs) =
    typeInfer =<< (Lam x <$> (typeInferAndId a)
                   <*> inExtendedCtx a (typeInferAndId rhs))
  typeInfer (Pi x a rhs) =
    typeInfer =<< (Pi x <$> (typeInferAndId a)
                   <*> inExtendedCtx a (typeInferAndId rhs))
  typeInfer t = typeInfer =<< mapM typeInferAndId t

-- Type inference for FlatTermF Term dispatches to that for FlatTermF TypedTerm
instance TypeInfer (FlatTermF Term) where
  typeInfer = typeInfer =<< mapM typeInferAndId t


-- Type inference for TermF TypedTerm is the main workhorse. Intuitively, this
-- represents the case where each immediate subterm of a term is labeled with
-- its (most general) type.
instance TypeInfer (TermF TypedTerm) where
  typeInfer (FTermF ftf) = typeInfer ftf
  typeInfer (App (TypedTerm _ x_tp) y) = applyPiTyped x_tp y
  typeInfer (Lambda x (TypedTerm a a_tp) (TypedTerm _ b)) =
    void (ensureSort a_tp) >> liftTCM1 scTermF (Pi x a b)
  typeInfer (Pi _ (TypedTerm a a_tp) (TypedTerm b b_tp)) =
    do s1 <- ensureSort a_tp
       s2 <- ensureSort b_tp
       -- NOTE: the rule for type-checking Pi types is that (Pi x a b) is a Prop
       -- when b is a Prop (this is a forall proposition), otherwise it is a
       -- (Type (max (sortOf a) (sortOf b)))
       liftTCM1 $ scSort $ if s2 == propSort then propSort else max s1 s2
  typeInfer (LocalVar i) =
    do (_, ctx) <- ask
       if i < length ctx then
         -- The ith type in the current variable typing context is well-typed
         -- relative to the suffix of the context after it, so we have to lift it
         -- (i.e., call incVars) to make it well-typed relative to all of ctx
         liftTCM3 incVars 0 (i+1) (ctx !! i)
         else
         throwTCError (DanglingVar (i - length env))
  typeInfer (Constant _ (TypedTerm _ tp) _) =
    -- FIXME: should we check that the type (3rd arg of Constant) is a type?
    return tp


-- Type inference for FlatTermF TypedTerm is the main workhorse for flat
-- terms. Intuitively, this represents the case where each immediate subterm of
-- a term has already been labeled with its (most general) type.
instance TypeInfer (FlatTermF TypedTerm) where
  typeInfer (GlobalDef d) =
    do ty <- liftTCM1 scTypeOfGlobal d
       _ <- ensureSort ty
       typeCheckWHNF ty
  typeInfer UnitValue = liftTCM0 scUnitType
  typeInfer UnitType = liftTCM1 scSort (mkSort 0)
  typeInfer (PairValue (TypedTerm _ tx) (TypedTerm ty)) =
    liftTCM2 scPairType tx ty
  typeInfer (PairType (TypedTerm _ tx) (TypedTerm ty)) =
    do sx <- ensureSort tx
       sy <- ensureSort ty
       liftTCM1 scSort (max sx sy)
  typeInfer EmptyValue = liftTCM0 scEmptyType
  typeInfer EmptyType = liftTCM1 scSort (mkSort 0)
  typeInfer (FieldValue f (TypedTerm _ tx) (TypedTerm _ ty)) =
    do checkField f
       liftTCM3 scFieldType f tx ty
  typeInfer (FieldType f (TypedTerm _ tx) (TypedTerm _ ty)) =
    do checkField f
       sx <- ensureSort tx
       sy <- ensureSort ty
       liftTCM1 scSort (max sx sy)
  typeInfer (PairLeft (TypedTerm _ tp)) =
    case asPairType tp of
      Just (t1, _) -> typeCheckWHNF t1
      _ -> throwTCError (NotTupleType tp)
  typeInfer (PairRight (TypedTerm _ tp)) =
    case asPairType tp of
      Just (_, t2) -> typeCheckWHNF t2
      _ -> throwTCError (NotTupleType tp)
  typeInfer (RecordSelector (TypedTerm _ tp) f@(TypedTerm f_trm _) =
    do checkField f
       maybe_str <- asStringLit <$> typeCheckWHNF f_trm
       f_str <- case maybe_str of
         Just x -> x
         Nothing -> throwTCError (BadRecordField f_trm)
       case asRecordType tp of
         Just m ->
           case Map.lookup f m of
             Nothing -> throwTCError $ BadRecordField f tp
             Just f_tp -> typeCheckWHNF f_tp
         _ -> throwTCError (NotRecordType tp)

  typeInfer (DataTypeApp dt params args) =
    -- Look up the DataType structure, check the length of the params and args,
    -- and then apply the cached Pi type of dt to params and args
    do maybe_dt <- liftTCM1 scFindDataType d
       dt <- case maybe_dt of
         Just dt -> return dt
         Nothing -> throwTCError $ NoSuchDataType d
       if length params == length (dtParams dt) &&
          length args == length (dtIndices dt) then return () else
         throwTCError $ BadParamsOrArgsLength True d params args
       -- NOTE: we assume dtType is already well-typed and in WHNF
       -- _ <- inferSort t
       -- t' <- typeCheckWHNF t
       foldM applyPiTyped (dtType dt) (params ++ args)

  typeInfer (CtorApp c params args) =
    -- Look up the Ctor structure, check the length of the params and args, and
    -- then apply the cached Pi type of ctor to params and args
    do maybe_ctor <- liftTCM1 scFindCtor c
       ctor <- case maybe_ctor of
         Just ctor -> return ctor
         Nothing -> throwTCError $ NoSuchCtor c
       if length params == length (ctorNumParams ctor) &&
          length args == length (ctorNumArgs ctor) then return () else
         throwTCError $ BadParamsOrArgsLength False c params args
       -- NOTE: we assume ctorType is already well-typed and in WHNF
       -- _ <- inferSort t
       -- t' <- typeCheckWHNF t
       foldM applyPiTyped (ctorType dt) (params ++ args)

  typeInfer (RecursorApp d params p_ret fs_cs ixs arg) =
    inferRecursorApp d params p_ret fs_cs ixs arg
  typeInfer (RecordType elems) =
    do sorts <- mapM (ensureSort . typedType . snd) elems
       liftTCM1 scSort (maximum sorts)
  typeInfer (RecordValue elems) =
    liftTCM1 scFlatTermF $ RecordType $
    map (\(f,TypedTerm _ tp) -> (f,tp)) elems
  typeInfer (RecordProj (TypedTerm _ t_tp) fld) =
    case asRecordType t_tp of
      Just (Map.lookup fld -> Just tp) -> return tp
      Just _ -> throwTCError $ NotRecordType t_tp
      Nothing -> throwTCError $ BadRecordField fld t_tp
  typeInfer (Sort s) = liftTCM1 scSort (sortOf s)
  typeInfer (NatLit _) = liftTCM0 scNatType
  typeInfer (ArrayValue (TypedTerm tp tp_tp) vs) =
    do n <- liftTCM1 scNat (fromIntegral (V.length vs))
       _ <- ensureSort tp_tp -- TODO: do we care about the level?
       tp' <- typeCheckWHNF tp
       forM_ vs $ \(TypedTerm _ v_tp) ->
         checkSubtype v_tp tp' (ArrayTypeMismatch tp' v_tp)
       liftTCM2 scVecType n tp'
  typeInfer (FloatLit{}) = liftTCM1 scFlatTermF preludeFloatType
  typeInfer (DoubleLit{}) = liftTCM1 scFlatTermF preludeDoubleType
  typeInfer (StringLit{}) = liftTCM1 scFlatTermF preludeStringType
  typeInfer (ExtCns ec) = typeCheckWHNF $ ecType ec


-- | Check that @tx=Pi v ty tz@ and that @y@ has type @ty@, and return @[y/v]tz@
applyPiTyped :: Term -> TypedTerm -> TCM Term
applyPiTyped tx (TypedTerm y ty) =
  case asPi tx of
    Just (_, aty, rty) -> do
      -- _ <- ensureSort aty -- NOTE: we assume tx is well-formed and WHNF
      -- aty' <- scTypeCheckWHNF aty
      checkSubtype ty aty (ArgTypeMismatch aty ty)
      liftTCM3 instantiateVar 0 y rty
    _ -> throwTCError (NotFuncType tx)

-- | Ensure that a 'Term' is a sort, and return that sort
ensureSort :: Term -> TCM Sort
ensureSort (asSort -> Just s) = return s
ensureSort tp = throwTCError $ NotSort tp

-- | Reduce a type to WHNF (using 'scWhnf'), also adding in some conversions for
-- operations on Nat literals that are useful in type-checking
typeCheckWHNF :: Term -> TCM Term
typeCheckWHNF t =
  do t' <- liftTCM2 rewriteSharedTerm (addConvs natConversions emptySimpset) t
  liftTCM1 scWhnf t'

-- | Check that one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s, and that they are both
-- already in WHNF. If the check fails, throw the given 'TCError'.
checkSubtype :: Term -> Term -> TCError -> TCM ()
checkSubtype t1 t2 err = helper (unwrapTermF t1) (unwrapTermF t2) where
  helper (Pi _ a1 b1) (Pi _ a2 b2) =
    checkConvertible a1 a2 err >>
    inExtendedContext a1 (checkConvertible b1 b2 err)
  helper (FTermF (Sort s1)) (FTermF (Sort s2)) | s1 <= s2 = return ()
  helper t1' t2' = checkConvertible t1' t2' err

-- | Check that two terms are "convertible for type-checking", meaning that they
-- are convertible up to 'natConversions'. Throw the given 'TCError' on failure.
checkConvertible :: Term -> Term -> TCError -> TCM ()
checkConvertible t1 t2 err =
  do are_conv <-
       liftTCM4 scConvertible (addConvs natConversions emptySimpset) True t1 t2
     if are_conv then return () else
       throwTCError err

-- | Check that a term has type @String@
checkField :: TypedTerm -> TCM ()
checkField (TypedTerm _ tf) =
  do string_tp <- liftTCM0 scStringType
     checkSubtype tf string_tp (NotStringType tf)

-- | Infer the type of a recursor application
inferRecursorApp :: Ident -> [TypedTerm] -> TypedTerm ->
                    [(Ident,TypedTerm)] -> [TypedTerm] -> TypedTerm ->
                    TCM Term
inferRecursorApp d params p_ret fs_cs ixs arg =
  do let err_term =
           Unshared $ fmap typedVal $ FTermF $
           RecursorApp d params p_ret fs_cs ixs arg
     maybe_dt <- liftTCM1 scFindDataType d
     dt <- case maybe_dt of
       Just dt -> dt
       Nothing -> throwTCError $ NoSuchDataType d

     -- Check that the params and ixs have the correct types by making sure
     -- they correspond to the input types of dt
     if length params == length (dtParams dt) &&
        length ixs == length (dtIndices dt) then return () else
       throwTCError $ MalformedRecursorArgs err_term
     _ <- foldM applyPiTyped (dtType dt) (params ++ ixs)

     -- Get the type of p_ret and make sure that it is of the form
     --
     -- (ix1::Ix1) -> .. -> (ixn::Ixn) -> d params ixs -> s
     --
     -- for some allowed sort s, where the Ix are the indices of of dt
     let p_ret_tp = typedType p_ret
     (p_ret_ctx, p_ret_s) <-
       case asPiList p_ret_tp of
         (ctx, (asSort -> Just s)) -> return (ctx, s)
         _ -> throwTCError $ MalformedRecursorRet err_term
     p_ret_tp_req <- liftTCM3 scRecursorRetTypeType dt params p_ret_s
     -- Technically this is an equality test, not a subtype test, but we
     -- use the precise sort used in p_ret_tp, so they are the same, and
     -- checkSubtype is handy...
     checkSubtype p_ret_tp p_ret_tp_req (MalformedRecursorRet err_term)
     if allowedElimSort dt s then return ()
       else throwTCError $ MalformedRecursorElimSort err_term

     -- Check that the elimination functions each have the right types, and
     -- that we have exactly one for each constructor of dt
     cs_fs_tps <- liftTCM3 scRecursorElimTypes dt params p_ret
     case map fst cs_fs \\ map fst cs_fs_tps of
       [] -> return ()
       cs -> throwTCError $ MalformedRecursorExtraCtors cs err_term
     forM cs_fs_tps $ \(c,req_tp) ->
       case lookup c cs_fs of
         Nothing ->
           throwTCError $ MalformedRecursorMissingCtor c err_term
         Just (TypedTerm _ f_tp) ->
           checkSubtype f_tp req_tp (MalformedRecursorCtorElim c err_term)

     -- Finally, check that arg has type (d params ixs), and return the
     -- type (p_ret ixs arg)
     let arg_tp = typedType arg
     arg_req_tp <-
       liftTCM1 scFlatTermF $ map typedVal $ DataTypeApp d params ixs
     checkSubtype arg_tp arg_req_tp (MalformedRecursorArg err_term)
     liftTCM2 scApplyAll (typedVal p_ret) (map typedVal (ixs ++ [arg]))
