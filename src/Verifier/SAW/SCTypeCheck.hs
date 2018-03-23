{-# LANGUAGE CPP #-}
{-# LANGUAGE ScopedTypeVariables #-}
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
import Control.Monad.State.Strict as State

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

-- | The monad for type-checking, which memoizes and can throw errors
type TCM a = State.StateT TCState (ExceptT TCError IO) a

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

-- | Throw a type-checking error
throwTCError :: TCError -> TCM a
throwTCError = lift . throwE

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
scTypeCheck sc t0 = runExceptT (scTypeCheck' sc [] t0)

-- | Like 'scTypeCheck', but type-check the term relative to a typing context,
-- which assigns types to free variables in the term
scTypeCheckInCtx :: SharedContext -> [Term] -> Term -> IO (Either TCError Term)
scTypeCheckInCtx sc ctx t0 = runExceptT $ scTypeCheck' sc ctx t0

-- | The main workhorse for 'scTypeCheck' and friends
scTypeCheck' :: SharedContext -> [Term] -> Term -> ExceptT TCError IO Term
scTypeCheck' sc env t0 = State.evalStateT (memo t0) Map.empty
  where
    -- Memoized type inference
    memo :: Term -> TCM Term
    memo (Unshared tf) = termf tf
    memo _t@(STApp{ stAppIndex = i, stAppTermF = tf}) =
      do table <- State.get
         case Map.lookup i table of
           Just x  -> return x
           Nothing ->
             do x <- termf tf
                x' <- scTypeCheckWHNF x
                State.modify (Map.insert i x')
                return x'

    -- Infer the type of a term and ensure that it is a sort
    sort :: Term -> TCM Sort
    sort t =
      do t_tp <- memo t
         case asSort t_tp of
           Just s -> return s
           Nothing -> throwTCError (NotSort t_tp)

    -- Helper function to lift IO computations
    io = lift . lift

    -- Check that tx = (Pi v ty tz) and that y has type ty, and return [y/v]tz
    applyPi :: Term -> Term -> TCM Term
    applyPi tx y = do
      ty <- memo y
      case asPi tx of
        Just (_, aty, rty) -> do
          _ <- sort aty -- TODO: do we care about the level?
          aty' <- scTypeCheckWHNF aty
          checkSubtype ty aty' (ArgTypeMismatch aty' ty)
          io $ instantiateVar sc 0 y rty
        _ -> throwTCError (NotFuncType tx)

    -- Check that one type is a subtype of another, throwing the given error if
    -- not. Note: we assume the types are already in WHNF.
    checkSubtype :: Term -> Term -> TCError -> TCM ()
    checkSubtype t1 t2 err = do
      ok <- io $ scSubtype sc ty ty'
      unless ok (throwTCError err)

    -- Check that a term has type String
    checkField :: Term -> TCM ()
    checkField f =
      do tf <- memo f
         string_tp <- io scStringType
         checkSubtype tf string_tp (NotStringType tf)

    -- The main type inference engine for term-level constructs
    termf :: TermF Term -> TCM Term
    termf tf =
      case tf of
        FTermF ftf -> ftermf ftf
        App x y ->
          do tx <- memo x
             applyPi tx y
        Lambda x a rhs ->
          do _ <- sort a
             -- NOTE: we call scTypeCheck' again here because we cannot reuse
             -- the memo table in an extended context
             b <- lift $ scTypeCheck' sc (a : env) rhs
             io $ scTermF sc (Pi x a b)
        Pi _ a rhs ->
          do s1 <- sort a
             -- NOTE: we call scTypeCheck' again here because we cannot reuse
             -- the memo table in an extended context
             s2 <- asSort =<< lift (scTypeCheck' sc (a : env) rhs)
             -- NOTE: the rule for type-checking Pi types is that (Pi x a b) is
             -- a Prop when b is a Prop (this is a forall proposition),
             -- otherwise it is a (Type (max (sortOf a) (sortOf b)))
             io $ scSort sc $ if s2 == propSort then propSort else max s1 s2
        LocalVar i
          | i < length env -> io $ incVars sc 0 (i + 1) (env !! i)
          | otherwise      -> throwTCError (DanglingVar (i - length env))
        Constant _ t _ -> memo t

    -- The type inference engine for built-in constructs
    ftermf :: FlatTermF Term -> TCM Term
    ftermf tf =
      case tf of
        GlobalDef d -> do
          ty <- io $ scTypeOfGlobal sc d
          _ <- sort ty
          scTypeCheckWHNF ty
        UnitValue -> io $ scUnitType sc
        UnitType -> io $ scSort sc (mkSort 0)
        PairValue x y -> do
          tx <- memo x
          ty <- memo y
          io $ scPairType sc tx ty
        PairType x y -> do
          sx <- sort x
          sy <- sort y
          io $ scSort sc (max sx sy)
        EmptyValue -> io $ scEmptyType sc
        EmptyType -> io $ scSort sc (mkSort 0)
        FieldValue f x y -> do
          checkField f
          tx <- memo x
          ty <- memo y
          io $ scFieldType sc f tx ty
        FieldType f x y -> do
          checkField f
          sx <- sort x
          sy <- sort y
          io $ scSort sc (max sx sy)
        PairLeft t -> do
          ty <- memo t
          case asPairType ty of
            Just (t1, _) -> scTypeCheckWHNF t1
            _ -> throwTCError (NotTupleType ty)
        PairRight t -> do
          ty <- memo t
          case asPairType ty of
            Just (_, t2) -> scTypeCheckWHNF t2
            _ -> throwTCError (NotTupleType ty)
        RecordSelector t f' -> do
          checkField f'
          maybe_f <- asStringLit <$> scTypeCheckWHNF f'
          f <- case maybe_f of
            Just f -> f
            Nothing -> throwTCError (BadRecordField f')
          ty <- memo t
          case asRecordType ty of
            Just m ->
              case Map.lookup f m of
                Nothing -> throwTCError $ BadRecordField f ty
                Just tp -> scTypeCheckWHNF tp
            _ -> throwTCError (NotRecordType ty)

        CtorApp c params args -> do
          t <- io $ scTypeOfCtor sc c
          _ <- sort () t -- TODO: do we care about the level?
          t' <- scTypeCheckWHNF t
          foldM applyPi t' (params ++ args)
        DataTypeApp dt params args -> do
          t <- io $ scTypeOfDataType sc dt
          _ <- sort t -- TODO: do we care about the level?
          t' <- scTypeCheckWHNF t
          foldM applyPi t' (params ++ args)
        RecursorApp d params p_ret fs_cs ixs arg -> do
          -- Look up the datatype
          maybe_dt <- scFindDataType sc d
          dt <- case maybe_dt of
            Just dt -> dt
            Nothing -> fail $ "Could not find datatype: " ++ show d

          -- Check that the params and ixs have the correct types by making sure
          -- they correspond to the input types of dt
          if length params /= length (dtParams dt) ||
             length ixs /= length (dtIndices dt) then
            throwTCError $ MalformedRecursorArgs (Unshared tf)
            else return ()
          _ <- foldM applyPi (dtType dt) (params ++ ixs)

          -- Get the type of p_ret and make sure that it is of the form
          --
          -- (ix1::Ix1) -> .. -> (ixn::Ixn) -> d params ixs -> s
          --
          -- for some allowed sort s, where the Ix are the indices of of dt
          p_ret_tp <- memo p_ret
          p_ret_s <-
            case asPiList p_ret_tp of
              (_, (asSort -> Just s)) -> return s
              _ -> throwTCError $ MalformedRecursorRet $ Unshared tf
          p_ret_tp_req <- scRecursorRetTypeType sc dt params p_ret_s
          -- Technically this is an equality test, not a subtype test, but we
          -- use the precise sort used in p_ret_tp, so they are the same, and
          -- checkSubtype is handy...
          checkSubtype p_ret_tp p_ret_tp_req
            (MalformedRecursorRet $ Unshared tf)
          if allowedElimSort dt s then return ()
            else throwTCError $ MalformedRecursorSort (Unshared tf)

          -- Check that the elimination functions each have the right types, and
          -- that we have exactly one for each constructor of dt
          cs_fs_tps <- scRecursorFunTypes sc dt params p_ret
          let extra_ctors = map fst cs_fst \\ map fst cs_fs_tps
          case extra_ctors of
            c:_ -> throwTCError $ MalformedRecursorExtraCtor c (Unshared tf)
            _ -> return ()
          forM cs_fs_tps $ \(c,req_tp) ->
            case lookup c cs_fs of
              Nothing ->
                throwTCError $ MalformedRecursorMissingCtor c (Unshared tf)
              Just f ->
                do f_tp <- memo f
                   checkSubtype f_tp req_tp
                     (MalformedRecursorCtorElim c (Unshared tf))

          -- Finally, check that arg has type (d params ixs), and return the
          -- type (p_ret ixs arg)
          arg_tp <- memo arg
          arg_req_tp <- scFlatTermF sc $ DataTypeApp d params ixs
          checkSubtype arg_tp arg_req_tp (MalformedRecursorArg (Unshared tf))
          scApplyAll sc p_ret (ixs ++ [arg])

        RecordType elems ->
          do sorts <- mapM (sort . snd) elems
             scSort sc (maximum sorts)

        RecordValue elems ->
          do elem_tps <- mapM (memo . snd) elems
             scFlatTermF sc (RecordType $ zip (map fst elems) elem_tps)
        RecordProj t fld ->
          do t_tp <- memo t
             case asRecordType t_tp of
               Just (Map.lookup fld -> Just tp) -> return tp
               Just _ -> throwTCError $ NotRecordType t_tp
               Nothing -> throwTCError $ BadRecordField f t_tp

        Sort s -> io $ scSort sc (sortOf s)
        NatLit _ -> io $ scNatType sc
        ArrayValue tp vs -> do
          n <- io $ scNat sc (fromIntegral (V.length vs))
          _ <- sort tp -- TODO: do we care about the level?
          tp' <- scTypeCheckWHNF tp
          forM_ vs $ \v_t ->
            do v_ty <- memo v_t
               checkSubtype v_ty tp' (ArrayTypeMismatch tp' v_ty)
          io $ scVecType sc n tp'
        FloatLit{}  -> io $ scFlatTermF sc preludeFloatType
        DoubleLit{} -> io $ scFlatTermF sc preludeDoubleType
        StringLit{} -> io $ scFlatTermF sc preludeStringType
        ExtCns ec   -> scTypeCheckWHNF $ ecType ec

-- | Reduce a type to WHNF (using 'scWhnf'), also adding in some conversions for
-- operations on Nat literals that are useful in type-checking
scTypeCheckWHNF :: Term -> TCM Term
scTypeCheckWHNF t = lift $ lift $ do
  t' <- rewriteSharedTerm sc (addConvs natConversions emptySimpset) t
  scWhnf sc t'

-- | Check that one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s, and that they are both
-- already in WHNF
scSubtype :: SharedContext -> Term -> Term -> IO Bool
scSubtype sc t1 t2 = helper (unwrapTermF t1) (unwrapTermF t2) where
  helper (Pi _ a1 b1) (Pi _ a2 b2) =
    (&&) <$> scConvertibleTC a1 a2 <*> scConvertibleTC b1 b2
  helper (FTermF (Sort s1)) (FTermF (Sort s2)) = return $ s1 <= s2
  helper t1' t2' = scConvertibleTC t1' t2'

-- | Check that two terms are "convertible for type-checking", meaning that they
-- are convertible up to 'natConversions'
scConvertibleTC :: SharedContext -> Term -> Term -> IO Bool
scConvertibleTC sc =
  scConvertible sc (addConvs natConversions emptySimpset) True
