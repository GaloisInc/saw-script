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
  , TCError
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

type TCState = Map TermIndex Term
type TCM a = State.StateT TCState (ExceptT TCError IO) a

data TCError
  = NotSort Term
  | NotFuncType Term
  | ArgTypeMismatch Term Term
  | NotTupleType Term
  | BadTupleIndex Int Term
  | NotRecordType Term
  | BadRecordField FieldName Term
  | ArrayTypeMismatch Term Term
  | DanglingVar Int

throwTCError :: TCError -> TCM a
throwTCError = lift . throwE

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

scTypeCheckError :: SharedContext -> Term
                 -> IO Term
scTypeCheckError sc t0 =
  either (fail . unlines . prettyTCError) return =<< scTypeCheck sc t0

-- | This version of the type checking function makes sure that the
-- entire term is well-formed, and that all internal type annotations
-- are correct. Types are evaluated to WHNF as necessary, and the
-- returned type is in WHNF.
scTypeCheck :: SharedContext -> Term -> IO (Either TCError Term)
scTypeCheck sc t0 = runExceptT (scTypeCheck' sc [] t0)

scTypeCheck' :: SharedContext -> [Term] -> Term -> ExceptT TCError IO Term
scTypeCheck' sc env t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: Term -> TCM Term
    memo (Unshared tf) = termf tf
    memo _t@(STApp{ stAppIndex = i, stAppTermF = tf}) =
      do table <- State.get
         case Map.lookup i table of
           Just x  -> return x
           Nothing ->
             do x <- termf tf
                x' <- whnf x
                State.modify (Map.insert i x')
                return x'
    sort :: Term -> TCM Sort
    sort t = asSort =<< memo t
    io = lift . lift
    whnf t = io $ do
      t' <- rewriteSharedTerm sc (addConvs natConversions emptySimpset) t
      scWhnf sc t'
    checkPi :: Term -> Term -> TCM Term
    checkPi tx y = do
      ty <- memo y
      case asPi tx of
        Just (_, aty, rty) -> do
          _ <- sort aty -- TODO: do we care about the level?
          aty' <- whnf aty
          checkEqTy ty aty' (ArgTypeMismatch aty' ty)
          io $ instantiateVar sc 0 y rty
        _ -> throwTCError (NotFuncType tx)
    checkEqTy :: Term -> Term -> TCError -> TCM ()
    checkEqTy ty ty' err = do
      ok <- io $ argMatch sc ty ty'
      unless ok (throwTCError err)
    termf :: TermF Term -> TCM Term
    termf tf =
      case tf of
        FTermF ftf -> ftermf ftf
        App x y ->
          do tx <- memo x
             checkPi tx y
        Lambda x a rhs ->
          do b <- lift $ scTypeCheck' sc (a : env) rhs
             io $ scTermF sc (Pi x a b)
        Pi _ a rhs ->
          do s1 <- asSort =<< memo a
             s2 <- asSort =<< lift (scTypeCheck' sc (a : env) rhs)
             io $ scSort sc (max s1 s2)
        LocalVar i
          | i < length env -> io $ incVars sc 0 (i + 1) (env !! i)
          | otherwise      -> throwTCError (DanglingVar (i - length env))
        Constant _ t _ -> memo t
    ftermf :: FlatTermF Term -> TCM Term
    ftermf tf =
      case tf of
        GlobalDef d -> do
          ty <- io $ scTypeOfGlobal sc d
          _ <- sort ty
          whnf ty
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
          tx <- memo x
          ty <- memo y
          io $ scFieldType sc f tx ty
        FieldType _ x y -> do
          sx <- sort x
          sy <- sort y
          io $ scSort sc (max sx sy)
        PairLeft t -> do
          ty <- memo t
          case ty of
            STApp{ stAppTermF = FTermF (PairType t1 _) } -> whnf t1
            _ -> throwTCError (NotTupleType ty)
        PairRight t -> do
          ty <- memo t
          case ty of
            STApp{ stAppTermF = FTermF (PairType _ t2) } -> whnf t2
            _ -> throwTCError (NotTupleType ty)
        RecordSelector t f' -> do
          f <- asStringLit =<< whnf f'
          ty <- memo t
          case asRecordType ty of
            Just m ->
              case Map.lookup f m of
                Nothing -> throwTCError $ BadRecordField f ty
                Just tp -> whnf tp
            _ -> throwTCError (NotRecordType ty)
        CtorApp c args -> do
          t <- io $ scTypeOfCtor sc c
          _ <- sort t -- TODO: do we care about the level?
          t' <- whnf t
          foldM (\ a b -> checkPi a b) t' args
        DataTypeApp dt args -> do
          t <- io $ scTypeOfDataType sc dt
          _ <- sort t -- TODO: do we care about the level?
          t' <- whnf t
          foldM (\ a b -> checkPi a b) t' args
        Sort s -> io $ scSort sc (sortOf s)
        NatLit _ -> io $ scNatType sc
        ArrayValue tp vs -> do
          n <- io $ scNat sc (fromIntegral (V.length vs))
          _ <- sort tp -- TODO: do we care about the level?
          tp' <- whnf tp
          tys <- traverse memo vs
          V.mapM_ (\ty -> checkEqTy ty tp' (ArrayTypeMismatch tp' ty)) tys
          io $ scFlatTermF sc (DataTypeApp preludeVecIdent [n, tp'])
        StringLit{} -> io $ scFlatTermF sc (DataTypeApp preludeStringIdent [])
        ExtCns ec   -> whnf $ ecType ec

argMatch :: SharedContext -> Term -> Term -> IO Bool
argMatch sc = term
  where
    whnf :: Term -> IO Term
    whnf t = do
      t' <- rewriteSharedTerm sc (addConvs natConversions emptySimpset) t
      scWhnf sc t'

    term :: Term -> Term -> IO Bool
    term t1 t2 = do
      t1' <- whnf t1
      t2' <- whnf t2
      term' t1' t2'

    term' :: Term -> Term -> IO Bool
    term' (Unshared tf1) (Unshared tf2) = termf tf1 tf2
    term' (Unshared tf1) (STApp{ stAppTermF = tf2 }) = termf tf1 tf2
    term' (STApp{ stAppTermF = tf1 }) (Unshared tf2) = termf tf1 tf2
    term' (STApp{ stAppIndex = i1, stAppTermF = tf1 })
          (STApp{ stAppIndex = i2, stAppTermF = tf2 })
      | i1 == i2  = return True
      | otherwise = termf tf1 tf2

    termf :: TermF Term -> TermF Term -> IO Bool
    termf (FTermF ftf1)    (FTermF ftf2)    = ftermf ftf1 ftf2
    termf (App      t1 u1) (App      t2 u2) = (&&) <$> term t1 t2 <*> term u1 u2
    termf (Lambda _ t1 u1) (Lambda _ t2 u2) = (&&) <$> term t1 t2 <*> term u1 u2
    termf (Pi     _ t1 u1) (Pi     _ t2 u2) = (&&) <$> term t1 t2 <*> term u1 u2
    termf (LocalVar i1)    (LocalVar i2)    = return (i1 == i2)
    termf _ _                               = return False

    ftermf :: FlatTermF Term -> FlatTermF Term -> IO Bool
    ftermf (Sort s) (Sort s') = return (s <= s')
    ftermf ftf1 ftf2 =
      case zipWithFlatTermF term ftf1 ftf2 of
        Nothing -> return False
        Just ftf3 -> Data.Foldable.and <$> sequenceA ftf3
