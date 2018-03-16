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
  = NotSort TermPath Term
  | NotFuncType TermPath Term
  | ArgTypeMismatch TermPath Term Term
  | NotTupleType TermPath Term
  | BadTupleIndex TermPath Int Term
  | NotStringType TermPath Term
  | NotRecordType TermPath Term
  | BadRecordField TermPath FieldName Term
  | ArrayTypeMismatch TermPath Term Term
  | DanglingVar TermPath Int

-- | Extract the 'TermPath' from a 'TCError'
tcErrorPath :: TCError -> TermPath
tcErrorPath (NotSort path _) = path
tcErrorPath (NotFuncType path _) = path
tcErrorPath (ArgTypeMismatch path _ _) = path
tcErrorPath (NotTupleType path _) = path
tcErrorPath (BadTupleIndex path _ _) = path
tcErrorPath (NotRecordType path _) = path
tcErrorPath (BadRecordField path _ _) = path
tcErrorPath (ArrayTypeMismatch path _ _) = path
tcErrorPath (DanglingVar path _) = path

-- | Throw a type-checking error
throwTCError :: TCError -> TCM a
throwTCError = lift . throwE

-- | Pretty-print a type-checking error
prettyTCError :: TCError -> [String]
prettyTCError e =
  case e of
    NotSort _ ty ->
      [ "Not a sort" , ishow ty ]
    NotFuncType _ ty ->
      [ "Function application with non-function type" , ishow ty ]
    ArgTypeMismatch _ ety aty ->
      [ "Function argument type" , ishow aty
      , "doesn't match expected type" , ishow ety
      ]
    NotTupleType _ ty ->
      [ "Tuple field projection with non-tuple type" , ishow ty ]
    BadTupleIndex _ n ty ->
      [ "Bad tuple index (" ++ show n ++ ") for type"
      , ishow ty
      ]
    NotRecordType _ ty ->
      [ "Record field projection with non-record type" , ishow ty ]
    BadRecordField _ n ty ->
      [ "Bad record field (" ++ show n ++ ") for type"
      , ishow ty
      ]
    ArrayTypeMismatch _ ety aty ->
      [ "Array element type" , ishow aty
      , "doesn't match declared array element type" , ishow ety
      ]
    DanglingVar _ n ->
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
scTypeCheck sc t0 = runExceptT (scTypeCheck' sc emptyTermPath [] t0)

-- | Like 'scTypeCheck', but type-check the term relative to a typing context,
-- which assigns types to free variables in the term
scTypeCheckInCtx :: SharedContext -> [Term] -> Term -> IO (Either TCError Term)
scTypeCheckInCtx sc ctx t0 = runExceptT $ scTypeCheck' sc emptyTermPath ctx t0

-- | The main workhorse for 'scTypeCheck' and friends
scTypeCheck' :: SharedContext -> TermPath -> [Term] -> Term ->
                ExceptT TCError IO Term
scTypeCheck' sc path0 env t0 = State.evalStateT (memo path0 t0) Map.empty
  where
    -- Memoized type inference
    memo :: TermPath -> Term -> TCM Term
    memo path (Unshared tf) = termf path tf
    memo path _t@(STApp{ stAppIndex = i, stAppTermF = tf}) =
      do table <- State.get
         case Map.lookup i table of
           Just x  -> return x
           Nothing ->
             do x <- termf path tf
                x' <- scTypeCheckWHNF x
                State.modify (Map.insert i x')
                return x'

    -- Infer the type of a term and ensure that it is a sort
    sort :: Path -> Term -> TCM Sort
    sort path t =
      do t_tp <- memo path t
         case asSort t_tp of
           Just s -> return s
           Nothing -> throwTCError (NotSort path t_tp)

    -- Helper function to lift IO computations
    io = lift . lift

    -- Check that tx = (Pi v ty tz), where y has type ty, and return [y/v]tz
    applyPi :: Path -> Term -> Term -> TCM Term
    applyPi path tx y = do
      ty <- memo path y
      case asPi tx of
        Just (_, aty, rty) -> do
          _ <- sort aty -- TODO: do we care about the level?
          aty' <- scTypeCheckWHNF aty
          checkSubtype ty aty' (ArgTypeMismatch path aty' ty)
          io $ instantiateVar sc 0 y rty
        _ -> throwTCError (NotFuncType path tx)

    -- Check that one type is a subtype of another, throwing the given error if
    -- not. Note: we assume the types are already in WHNF.
    checkSubtype :: Term -> Term -> TCError -> TCM ()
    checkSubtype t1 t2 err = do
      ok <- io $ scSubtype sc ty ty'
      unless ok (throwTCError err)

    -- Check that a term has type String
    checkField :: Path -> Term -> TCM ()
    checkField path f =
      do tf <- memo (extendTermPath 0 path) f
         string_tp <- io scStringType
         checkSubtype tf string_tp (NotStringType path tf)

    -- The main type inference engine for term-level constructs
    termf :: Path -> TermF Term -> TCM Term
    termf path tf =
      case tf of
        FTermF ftf -> ftermf path ftf
        App x y ->
          do tx <- memo (extendTermPath 0 path) x
             applyPi (extendTermPath 1 path) tx y
        Lambda x a rhs ->
          do _ <- sort (extendTermPath 0 path) a
             -- NOTE: we call scTypeCheck' again here because we cannot reuse
             -- the memo table in an extended context
             b <- lift $ scTypeCheck' sc (extendTermPath 1 path) (a : env) rhs
             io $ scTermF sc (Pi x a b)
        Pi _ a rhs ->
          do s1 <- sort (extendTermPath 0 path) a
             -- NOTE: we call scTypeCheck' again here because we cannot reuse
             -- the memo table in an extended context
             s2 <- asSort =<< lift (scTypeCheck' sc (extendTermPath 1 path)
                                    (a : env) rhs)
             -- NOTE: the rule for type-checking Pi types is that (Pi x a b) is
             -- a Prop when b is a Prop (this is a forall proposition),
             -- otherwise it is a (Type (max (sortOf a) (sortOf b)))
             io $ scSort sc $ if s2 == propSort then propSort else max s1 s2
        LocalVar i
          | i < length env -> io $ incVars sc 0 (i + 1) (env !! i)
          | otherwise      -> throwTCError (DanglingVar path (i - length env))
        Constant _ t _ -> memo t

    -- The type inference engine for built-in constructs
    ftermf :: Path -> FlatTermF Term -> TCM Term
    ftermf path tf =
      case tf of
        GlobalDef d -> do
          ty <- io $ scTypeOfGlobal sc d
          _ <- sort ty
          scTypeCheckWHNF ty
        UnitValue -> io $ scUnitType sc
        UnitType -> io $ scSort sc (mkSort 0)
        PairValue x y -> do
          tx <- memo (extendTermPath 0 path) x
          ty <- memo (extendTermPath 1 path) y
          io $ scPairType sc tx ty
        PairType x y -> do
          sx <- sort (extendTermPath 0 path) x
          sy <- sort (extendTermPath 1 path) y
          io $ scSort sc (max sx sy)
        EmptyValue -> io $ scEmptyType sc
        EmptyType -> io $ scSort sc (mkSort 0)
        FieldValue f x y -> do
          checkField f
          tx <- memo (extendTermPath 1 path) x
          ty <- memo (extendTermPath 2 path) y
          io $ scFieldType sc f tx ty
        FieldType f x y -> do
          checkField f
          sx <- sort (extendTermPath 1 path) x
          sy <- sort (extendTermPath 2 path) y
          io $ scSort sc (max sx sy)
        PairLeft t -> do
          ty <- memo (extendTermPath 0 path) t
          case asPairType ty of
            Just (t1, _) -> scTypeCheckWHNF t1
            _ -> throwTCError (NotTupleType path ty)
        PairRight t -> do
          ty <- memo (extendTermPath 0 path) t
          case asPairType ty of
            Just (_, t2) -> scTypeCheckWHNF t2
            _ -> throwTCError (NotTupleType path ty)
        RecordSelector t f' -> do
          checkField (extendTermPath 0 path) f'
          maybe_f <- asStringLit <$> scTypeCheckWHNF f'
          f <- case maybe_f of
            Just f -> f
            Nothing -> throwTCError (BadRecordField path f')
          ty <- memo (extendTermPath 1 path) t
          case asRecordType ty of
            Just m ->
              case Map.lookup f m of
                Nothing -> throwTCError $ BadRecordField path f ty
                Just tp -> scTypeCheckWHNF tp
            _ -> throwTCError (NotRecordType (extendTermPath 0 path) ty)
        CtorApp c args -> do
          t <- io $ scTypeOfCtor sc c
          _ <- sort () t -- TODO: do we care about the level?
          t' <- scTypeCheckWHNF t
          foldM (\ (i,a) b ->
                  applyPi (extendTermPath i path) a b) t' (zip [0..] args)
        DataTypeApp dt args -> do
          t <- io $ scTypeOfDataType sc dt
          _ <- sort t -- TODO: do we care about the level?
          t' <- scTypeCheckWHNF t
          foldM (\ (i,a) b ->
                  applyPi (extendTermPath i path) a b) t' (zip [0..] args)
        Sort s -> io $ scSort sc (sortOf s)
        NatLit _ -> io $ scNatType sc
        ArrayValue tp vs -> do
          n <- io $ scNat sc (fromIntegral (V.length vs))
          _ <- sort (extendTermPath 0 path) tp -- TODO: do we care about the level?
          tp' <- scTypeCheckWHNF tp
          forM_ [0 .. V.length vs - 1] $ \i ->
            do v_ty <- memo (extendTermPath (i+1) path) (vs V.! i)
               checkSubtype v_ty tp' (ArrayTypeMismatch tp' ty)
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
    (&&) <$> scConvertible a1 a2 <*> scConvertible b1 b2
  helper (FTermF (Sort s1)) (FTermF (Sort s2)) = return $ s1 <= s2
  helper t1' t2' = scConvertible t1' t2'

-- | Check that two terms are convertable, assuming they both have the same type
-- and are both in WHNF
scConvertible :: SharedContext -> Term -> Term -> IO Bool
scConvertible sc = term
  where
    term' :: Term -> Term -> IO Bool
    term' t1 t2 = do
      t1' <- scTypeCheckWHNF t1
      t2' <- scTypeCheckWHNF t2
      term t1' t2'

    term :: Term -> Term -> IO Bool
    term (Unshared tf1) (Unshared tf2) = termf tf1 tf2
    term (Unshared tf1) (STApp{ stAppTermF = tf2 }) = termf tf1 tf2
    term (STApp{ stAppTermF = tf1 }) (Unshared tf2) = termf tf1 tf2
    term (STApp{ stAppIndex = i1, stAppTermF = tf1 })
          (STApp{ stAppIndex = i2, stAppTermF = tf2 })
      | i1 == i2  = return True
      | otherwise = termf tf1 tf2

    termf :: TermF Term -> TermF Term -> IO Bool
    termf (FTermF ftf1)    (FTermF ftf2)    = ftermf ftf1 ftf2
    termf (App      t1 u1) (App      t2 u2) = (&&) <$> term' t1 t2 <*> term' u1 u2
    termf (Lambda _ t1 u1) (Lambda _ t2 u2) = (&&) <$> term' t1 t2 <*> term' u1 u2
    termf (Pi     _ t1 u1) (Pi     _ t2 u2) = (&&) <$> term' t1 t2 <*> term' u1 u2
    termf (LocalVar i1)    (LocalVar i2)    = return (i1 == i2)
    termF (Constant _ d _) t                = term d (Unshared t)
    termF t                (Constant _ d _) = term (Unshared t) d
    termf _                _                = return False

    ftermf :: FlatTermF Term -> FlatTermF Term -> IO Bool
    ftermf ftf1 ftf2 =
      case zipWithFlatTermF term_whnf ftf1 ftf2 of
        Nothing -> return False
        Just ftf3 -> Data.Foldable.and <$> sequenceA ftf3
