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
  , scTypeCheckWHNF
  , scConvertible
  , TCError(..)
  , prettyTCError
  , throwTCError
  , TCM
  , runTCM
  , askCtx
  , askModName
  , inExtendedCtx
  , LiftTCM(..)
  , TypedTerm(..)
  , TypeInfer(..)
  , checkSubtype
  , ensureSort
  , applyPiTyped
  ) where

import Control.Applicative
import Control.Monad.Trans.Except
import Control.Monad.State.Strict
import Control.Monad.Reader

import Data.List
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
import Verifier.SAW.Module

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
  ReaderT (SharedContext, Maybe ModuleName, [(String,Term)])
  (StateT TCState (ExceptT TCError IO)) a

-- | Run a type-checking computation in a given context, starting from the empty
-- memoization table
runTCM :: TCM a -> SharedContext -> Maybe ModuleName -> [(String,Term)] ->
          IO (Either TCError a)
runTCM m sc mnm ctx =
  runExceptT $ evalStateT (runReaderT m (sc, mnm, ctx)) Map.empty

-- | Read the current typing context
askCtx :: TCM [(String,Term)]
askCtx = (\(_,_,ctx) -> ctx) <$> ask

-- | Read the current module name
askModName :: TCM (Maybe ModuleName)
askModName = (\(_,mnm,_) -> mnm) <$> ask

-- | Run a type-checking computation in a typing context extended with a new
-- variable with the given type. This throws away the memoization table while
-- running the sub-computation, as memoization tables are tied to specific sets
-- of bindings.
inExtendedCtx :: String -> Term -> TCM a -> TCM a
inExtendedCtx x tp m =
  do saved_table <- get
     put Map.empty
     a <- local (\(sc,mnm,ctx) -> (sc, mnm, (x,tp):ctx)) m
     put saved_table
     return a

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
  | NotFuncType Term
  | ArgTypeMismatch Term Term
  | NotTupleType Term
  | BadTupleIndex Int Term
  | NotStringType Term
  | NotStringLit Term
  | NotRecordType Term
  | BadRecordField FieldName Term
  | ArrayTypeMismatch Term Term
  | DanglingVar Int
  | UnboundName String
  | ConstraintFailure Term Term
  | EmptyVectorLit
  | NoSuchDataType Ident
  | NoSuchCtor Ident
  | NotFullyApplied Ident
  | NotFullyAppliedRec Ident
  | BadParamsOrArgsLength Bool Ident [Term] [Term]
  | MalformedRecursor Term String
  | DeclError String String

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
    NotStringType ty ->
      [ "Field with non-string type", ishow ty ]
    NotStringLit trm ->
      [ "Record selector is not a string literal", ishow trm ]
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
    UnboundName str -> [ "Unbound name: " ++ str]
    ConstraintFailure tp1 tp2 ->
      [ "Inferred type", ishow tp1,
        "Not a subtype of expected type", ishow tp2 ]
    EmptyVectorLit -> [ "Empty vector literal" ]
    NoSuchDataType d -> [ "No such data type: " ++ show d]
    NoSuchCtor c -> [ "No such constructor: " ++ show c]
    NotFullyApplied i ->
      [ "Constructor or datatype not fully applied: " ++ show i ]
    NotFullyAppliedRec i ->
      [ "Recursor not fully applied: " ++ show i ]
    BadParamsOrArgsLength is_dt ident params args ->
      [ "Wrong number of parameters or arguments to "
        ++ (if is_dt then "datatype" else "constructor") ++ ": ",
        ishow (Unshared $ FTermF $
               (if is_dt then DataTypeApp else CtorApp) ident params args)
      ]
    MalformedRecursor trm reason ->
      [ "Malformed recursor application", ishow trm, reason ]
    DeclError nm reason -> ["Malformed declaration for " ++ nm, reason]
  where
    ishow = (' ':) . (' ':) . scPrettyTerm defaultPPOpts


-- | Infer the type of a term using 'scTypeCheck', calling 'fail' on failure
scTypeCheckError :: SharedContext -> Term -> IO Term
scTypeCheckError sc t0 =
  either (fail . unlines . prettyTCError) return =<< scTypeCheck sc Nothing t0

-- | Infer the type of a 'Term', ensuring in the process that the entire term is
-- well-formed and that all internal type annotations are correct. Types are
-- evaluated to WHNF as necessary, and the returned type is in WHNF.
scTypeCheck :: SharedContext -> Maybe ModuleName -> Term ->
               IO (Either TCError Term)
scTypeCheck sc mnm = scTypeCheckInCtx sc mnm []

-- | Like 'scTypeCheck', but type-check the term relative to a typing context,
-- which assigns types to free variables in the term
scTypeCheckInCtx :: SharedContext -> Maybe ModuleName -> [(String,Term)] ->
                    Term -> IO (Either TCError Term)
scTypeCheckInCtx sc mnm ctx t0 = runTCM (typeInfer t0) sc mnm ctx

-- | A pair of a 'Term' and its type
data TypedTerm = TypedTerm { typedVal :: Term, typedType :: Term }

-- | The class of things that we can infer types of. The 'typeInfer' method
-- returns the most general (with respect to subtyping) type of its input.
class TypeInfer a where
  -- | Infer the type of an @a@
  typeInfer :: a -> TCM Term
  -- | Infer the type of an @a@ and complete it to a 'Term'
  typeInferComplete :: a -> TCM TypedTerm


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
    typeInfer =<< (Lambda x <$> (typeInferComplete a)
                   <*> inExtendedCtx x a (typeInferComplete rhs))
  typeInfer (Pi x a rhs) =
    typeInfer =<< (Pi x <$> (typeInferComplete a)
                   <*> inExtendedCtx x a (typeInferComplete rhs))
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
  typeInfer (App (TypedTerm _ x_tp) y) = applyPiTyped x_tp y
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
         throwTCError (DanglingVar (i - length ctx))
  typeInfer (Constant _ (TypedTerm _ tp) _) =
    -- FIXME: should we check that the type (3rd arg of Constant) is a type?
    return tp
  typeInferComplete tf =
    TypedTerm <$> liftTCM scTermF (fmap typedVal tf) <*> typeInfer tf


-- Type inference for FlatTermF TypedTerm is the main workhorse for flat
-- terms. Intuitively, this represents the case where each immediate subterm of
-- a term has already been labeled with its (most general) type.
instance TypeInfer (FlatTermF TypedTerm) where
  typeInfer (GlobalDef d) =
    do ty <- liftTCM scTypeOfGlobal d
       _ <- ensureSort ty
       typeCheckWHNF ty
  typeInfer UnitValue = liftTCM scUnitType
  typeInfer UnitType = liftTCM scSort (mkSort 0)
  typeInfer (PairValue (TypedTerm _ tx) (TypedTerm _ ty)) =
    liftTCM scPairType tx ty
  typeInfer (PairType (TypedTerm _ tx) (TypedTerm _ ty)) =
    do sx <- ensureSort tx
       sy <- ensureSort ty
       liftTCM scSort (max sx sy)
  typeInfer EmptyValue = liftTCM scEmptyType
  typeInfer EmptyType = liftTCM scSort (mkSort 0)
  typeInfer (FieldValue f (TypedTerm _ tx) (TypedTerm _ ty)) =
    do checkField f
       liftTCM scFieldType (typedVal f) tx ty
  typeInfer (FieldType f (TypedTerm _ tx) (TypedTerm _ ty)) =
    do checkField f
       sx <- ensureSort tx
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
  typeInfer (RecordSelector (TypedTerm _ tp) f@(TypedTerm f_trm _)) =
    do checkField f
       maybe_str <- asStringLit <$> typeCheckWHNF f_trm
       f_str <- case maybe_str of
         Just x -> return x
         Nothing -> throwTCError (NotStringLit f_trm)
       case asRecordType tp of
         Just m ->
           case Map.lookup f_str m of
             Nothing -> throwTCError $ BadRecordField f_str tp
             Just f_tp -> typeCheckWHNF f_tp
         _ -> throwTCError (NotRecordType tp)

  typeInfer (DataTypeApp d params args) =
    -- Look up the DataType structure, check the length of the params and args,
    -- and then apply the cached Pi type of dt to params and args
    do maybe_dt <- liftTCM scFindDataType d
       dt <- case maybe_dt of
         Just dt -> return dt
         Nothing -> throwTCError $ NoSuchDataType d
       if length params == length (dtParams dt) &&
          length args == length (dtIndices dt) then return () else
         throwTCError $
         BadParamsOrArgsLength True d (map typedVal params) (map typedVal args)
       -- NOTE: we assume dtType is already well-typed and in WHNF
       -- _ <- inferSort t
       -- t' <- typeCheckWHNF t
       foldM applyPiTyped (dtType dt) (params ++ args)

  typeInfer (CtorApp c params args) =
    -- Look up the Ctor structure, check the length of the params and args, and
    -- then apply the cached Pi type of ctor to params and args
    do maybe_ctor <- liftTCM scFindCtor c
       ctor <- case maybe_ctor of
         Just ctor -> return ctor
         Nothing -> throwTCError $ NoSuchCtor c
       if length params == ctorNumParams ctor &&
          length args == ctorNumArgs ctor then return () else
         throwTCError $
         BadParamsOrArgsLength False c (map typedVal params) (map typedVal args)
       -- NOTE: we assume ctorType is already well-typed and in WHNF
       -- _ <- inferSort t
       -- t' <- typeCheckWHNF t
       foldM applyPiTyped (ctorType ctor) (params ++ args)

  typeInfer (RecursorApp d params p_ret cs_fs ixs arg) =
    inferRecursorApp d params p_ret cs_fs ixs arg
  typeInfer (RecordType elems) =
    do sorts <- mapM (ensureSort . typedType . snd) elems
       liftTCM scSort (maximum sorts)
  typeInfer (RecordValue elems) =
    liftTCM scFlatTermF $ RecordType $
    map (\(f,TypedTerm _ tp) -> (f,tp)) elems
  typeInfer (RecordProj (TypedTerm _ t_tp) fld) =
    case asRecordType t_tp of
      Just (Map.lookup fld -> Just tp) -> return tp
      Just _ -> throwTCError $ NotRecordType t_tp
      Nothing -> throwTCError $ BadRecordField fld t_tp
  typeInfer (Sort s) = liftTCM scSort (sortOf s)
  typeInfer (NatLit _) = liftTCM scNatType
  typeInfer (ArrayValue (TypedTerm tp tp_tp) vs) =
    do n <- liftTCM scNat (fromIntegral (V.length vs))
       _ <- ensureSort tp_tp -- TODO: do we care about the level?
       tp' <- typeCheckWHNF tp
       forM_ vs $ \(TypedTerm _ v_tp) ->
         checkSubtype v_tp tp' (ArrayTypeMismatch tp' v_tp)
       liftTCM scVecType n tp'
  typeInfer (FloatLit{}) = liftTCM scFlatTermF preludeFloatType
  typeInfer (DoubleLit{}) = liftTCM scFlatTermF preludeDoubleType
  typeInfer (StringLit{}) = liftTCM scFlatTermF preludeStringType
  typeInfer (ExtCns ec) =
    -- FIXME: should we check that the type of ecType is a sort?
    typeCheckWHNF $ typedVal $ ecType ec

  typeInferComplete ftf =
    TypedTerm <$> liftTCM scFlatTermF (fmap typedVal ftf) <*> typeInfer ftf

-- | Check that @tx=Pi v ty tz@ and that @y@ has type @ty@, and return @[y/v]tz@
applyPiTyped :: Term -> TypedTerm -> TCM Term
applyPiTyped tx (TypedTerm y ty) =
  case asPi tx of
    Just (_, aty, rty) -> do
      -- _ <- ensureSort aty -- NOTE: we assume tx is well-formed and WHNF
      -- aty' <- scTypeCheckWHNF aty
      checkSubtype ty aty (ArgTypeMismatch aty ty)
      liftTCM instantiateVar 0 y rty
    _ -> throwTCError (NotFuncType tx)

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
  do t' <- rewriteSharedTerm sc (addConvs natConversions emptySimpset) t
     scWhnf sc t'

-- | Check that one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s, and that they are both
-- already in WHNF. If the check fails, throw the given 'TCError'.
checkSubtype :: Term -> Term -> TCError -> TCM ()
checkSubtype (unwrapTermF -> Pi x1 a1 b1) (unwrapTermF -> Pi _ a2 b2) err =
    checkConvertible a1 a2 err >>
    inExtendedCtx x1 a1 (checkSubtype b1 b2 err)
checkSubtype (asSort -> Just s1) (asSort -> Just s2) _ | s1 <= s2 = return ()
checkSubtype t1' t2' err = checkConvertible t1' t2' err

-- | Check that two terms are "convertible for type-checking", meaning that they
-- are convertible up to 'natConversions'. Throw the given 'TCError' on failure.
checkConvertible :: Term -> Term -> TCError -> TCM ()
checkConvertible t1 t2 err =
  do are_conv <- liftTCM scConvertibleEval scTypeCheckWHNF True t1 t2
     if are_conv then return () else throwTCError err

-- | Check that a term has type @String@
checkField :: TypedTerm -> TCM ()
checkField (TypedTerm _ tf) =
  do string_tp <- liftTCM scStringType
     checkSubtype tf string_tp (NotStringType tf)

-- | Infer the type of a recursor application
inferRecursorApp :: Ident -> [TypedTerm] -> TypedTerm ->
                    [(Ident,TypedTerm)] -> [TypedTerm] -> TypedTerm ->
                    TCM Term
inferRecursorApp d params p_ret cs_fs ixs arg =
  do let mk_err str =
           MalformedRecursor
           (Unshared $ fmap typedVal $ FTermF $
            RecursorApp d params p_ret cs_fs ixs arg) str
     maybe_dt <- liftTCM scFindDataType d
     dt <- case maybe_dt of
       Just dt -> return dt
       Nothing -> throwTCError $ NoSuchDataType d

     -- Check that the params and ixs have the correct types by making sure
     -- they correspond to the input types of dt
     if length params == length (dtParams dt) &&
        length ixs == length (dtIndices dt) then return () else
       throwTCError $ mk_err "Incorrect number of params or indices"
     _ <- foldM applyPiTyped (dtType dt) (params ++ ixs)

     -- Get the type of p_ret and make sure that it is of the form
     --
     -- (ix1::Ix1) -> .. -> (ixn::Ixn) -> d params ixs -> s
     --
     -- for some allowed sort s, where the Ix are the indices of of dt
     let p_ret_tp = typedType p_ret
     p_ret_s <-
       case asPiList p_ret_tp of
         (_, (asSort -> Just s)) -> return s
         _ -> throwTCError $ mk_err "Incorrectly typed motive function"
     p_ret_tp_req <-
       liftTCM scRecursorRetTypeType dt (map typedVal params) p_ret_s
     -- Technically this is an equality test, not a subtype test, but we
     -- use the precise sort used in p_ret_tp, so they are the same, and
     -- checkSubtype is handy...
     checkSubtype p_ret_tp p_ret_tp_req (mk_err
                                         "Incorrectly typed motive function")
     if allowedElimSort dt p_ret_s then return ()
       else throwTCError $ mk_err "Disallowed propositional elimination"

     -- Check that the elimination functions each have the right types, and
     -- that we have exactly one for each constructor of dt
     cs_fs_tps <-
       liftTCM scRecursorElimTypes d (map typedVal params) (typedVal p_ret)
     case map fst cs_fs \\ map fst cs_fs_tps of
       [] -> return ()
       cs -> throwTCError $ mk_err ("Extra constructors: " ++ show cs)
     forM_ cs_fs_tps $ \(c,req_tp) ->
       case lookup c cs_fs of
         Nothing ->
           throwTCError $ mk_err ("Missing constructor: " ++ show c)
         Just (TypedTerm _ f_tp) ->
           checkSubtype f_tp req_tp
           (mk_err $ "Incorrectly typed eliminator for constructor " ++ show c)

     -- Finally, check that arg has type (d params ixs), and return the
     -- type (p_ret ixs arg)
     let arg_tp = typedType arg
     arg_req_tp <-
       liftTCM scFlatTermF $ fmap typedVal $ DataTypeApp d params ixs
     checkSubtype arg_tp arg_req_tp (mk_err "Incorrectly typed argument")
     liftTCM scApplyAll (typedVal p_ret) (map typedVal (ixs ++ [arg]))
