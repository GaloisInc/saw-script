{-# LANGUAGE ScopedTypeVariables #-}
{- |
Module      : Verifier.SAW.SCTypeCheck
Copyright   : Galois, Inc. 2012-2014
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

import Data.Foldable (maximum, and)
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Traversable (Traversable(..))
import qualified Data.Vector as V
import Prelude hiding (mapM, maximum)

import Verifier.SAW.Conversion (natConversions)
import Verifier.SAW.Prelude.Constants
import Verifier.SAW.Recognizer
import Verifier.SAW.Rewriter
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST hiding (incVars, instantiateVarList)

type TCState s = Map TermIndex (SharedTerm s)
type TCM s a = State.StateT (TCState s) (ExceptT (TCError s) IO) a

data TCError s
  = NotSort (SharedTerm s)
  | NotFuncType (SharedTerm s)
  | ArgTypeMismatch (SharedTerm s) (SharedTerm s)
  | NotTupleType (SharedTerm s)
  | BadTupleIndex Int (SharedTerm s)
  | NotRecordType (SharedTerm s)
  | BadRecordField FieldName (SharedTerm s)
  | ArrayTypeMismatch (SharedTerm s) (SharedTerm s)
  | DanglingVar Int

throwTCError :: TCError s -> TCM s a
throwTCError = lift . throwE

prettyTCError :: TCError s -> [String]
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
    ishow = (' ':) . (' ':) . show

scTypeCheckError :: forall s. SharedContext s -> SharedTerm s
                 -> IO (SharedTerm s)
scTypeCheckError sc t0 =
  either (error . unlines . prettyTCError) id <$> scTypeCheck sc t0

-- | This version of the type checking function makes sure that the
-- entire term is well-formed, and that all internal type annotations
-- are correct. Types are evaluated to WHNF as necessary, and the
-- returned type is in WHNF.
scTypeCheck :: forall s. SharedContext s -> SharedTerm s
            -> IO (Either (TCError s) (SharedTerm s))
scTypeCheck sc t0 = runExceptT (scTypeCheck' sc [] t0)

scTypeCheck' :: forall s. SharedContext s -> [SharedTerm s] -> SharedTerm s
             -> ExceptT (TCError s) IO (SharedTerm s)
scTypeCheck' sc env t0 = State.evalStateT (memo t0) Map.empty
  where
    memo :: SharedTerm s -> TCM s (SharedTerm s)
    memo (Unshared tf) = termf tf
    memo _t@(STApp i tf) =
      do table <- State.get
         case Map.lookup i table of
           Just x  -> return x
           Nothing ->
             do x <- termf tf
                x' <- whnf x
                State.modify (Map.insert i x')
                return x'
    sort :: SharedTerm s -> TCM s Sort
    sort t = asSort =<< memo t
    io = lift . lift
    whnf t = io $ do
      t' <- rewriteSharedTerm sc (addConvs natConversions emptySimpset) t
      scWhnf sc t'
    checkPi :: SharedTerm s -> SharedTerm s -> TCM s (SharedTerm s)
    checkPi tx y = do
      ty <- memo y
      case asPi tx of
        Just (_, aty, rty) -> do
          _ <- sort aty -- TODO: do we care about the level?
          aty' <- whnf aty
          checkEqTy ty aty' (ArgTypeMismatch aty' ty)
          io $ instantiateVar sc 0 y rty
        _ -> throwTCError (NotFuncType tx)
    checkEqTy :: SharedTerm s -> SharedTerm s -> TCError s -> TCM s ()
    checkEqTy ty ty' err = do
      ok <- io $ argMatch sc ty ty'
      unless ok (throwTCError err)
    termf :: TermF (SharedTerm s) -> TCM s (SharedTerm s)
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
        -- TODO: this won't support dependent Let bindings
        -- TODO: should the bindings be reversed?
        -- TODO: check that all defs have the annotated type
        Let defs rhs -> lift $ scTypeCheck' sc (reverse dtys ++ env) rhs
          where dtys = map defType defs
        LocalVar i
          | i < length env -> io $ incVars sc 0 (i + 1) (env !! i)
          | otherwise      -> throwTCError (DanglingVar (i - length env))
        Constant _ t _ -> memo t
    ftermf :: FlatTermF (SharedTerm s) -> TCM s (SharedTerm s)
    ftermf tf =
      case tf of
        GlobalDef d -> do
          ty <- io $ scTypeOfGlobal sc d
          _ <- sort ty
          whnf ty
        TupleValue l -> io . scTupleType sc =<< traverse memo l
        TupleType [] -> io $ scSort sc (mkSort 0)
        TupleType l -> io . scSort sc . maximum =<< traverse sort l
        TupleSelector t i -> do
          ty <- memo t
          case ty of
            STApp _ (FTermF (TupleType ts)) -> do
              unless (i <= length ts) $ throwTCError $ BadTupleIndex i ty
              whnf (ts !! (i-1))
            _ -> throwTCError (NotTupleType ty)
        RecordValue m -> io . scRecordType sc =<< traverse memo m
        RecordSelector t f -> do
          ty <- memo t
          case ty of
            STApp _ (FTermF (RecordType m)) -> 
              case Map.lookup f m of
                Nothing -> throwTCError $ BadRecordField f ty
                Just tp -> whnf tp
            _ -> throwTCError (NotRecordType ty)
        RecordType m | Map.null m -> io $ scSort sc (mkSort 0)
        RecordType m -> io . scSort sc . maximum =<< traverse sort m
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
        FloatLit{}  -> io $ scFlatTermF sc (DataTypeApp preludeFloatIdent  [])
        DoubleLit{} -> io $ scFlatTermF sc (DataTypeApp preludeDoubleIdent [])
        StringLit{} -> io $ scFlatTermF sc (DataTypeApp preludeStringIdent [])
        ExtCns ec   -> whnf $ ecType ec

argMatch :: forall s. SharedContext s -> SharedTerm s -> SharedTerm s -> IO Bool
argMatch sc = term
  where
    whnf :: SharedTerm s -> IO (SharedTerm s)
    whnf t = do
      t' <- rewriteSharedTerm sc (addConvs natConversions emptySimpset) t
      scWhnf sc t'

    term :: SharedTerm s -> SharedTerm s -> IO Bool
    term t1 t2 = do
      t1' <- whnf t1
      t2' <- whnf t2
      term' t1' t2'

    term' :: SharedTerm s -> SharedTerm s -> IO Bool
    term' (Unshared tf1) (Unshared tf2) = termf tf1 tf2
    term' (Unshared tf1) (STApp _  tf2) = termf tf1 tf2
    term' (STApp _  tf1) (Unshared tf2) = termf tf1 tf2
    term' (STApp i1 tf1) (STApp i2 tf2)
      | i1 == i2  = return True
      | otherwise = termf tf1 tf2

    termf :: TermF (SharedTerm s) -> TermF (SharedTerm s) -> IO Bool
    termf (FTermF ftf1)    (FTermF ftf2)    = ftermf ftf1 ftf2
    termf (App      t1 u1) (App      t2 u2) = (&&) <$> term t1 t2 <*> term u1 u2
    termf (Lambda _ t1 u1) (Lambda _ t2 u2) = (&&) <$> term t1 t2 <*> term u1 u2
    termf (Pi     _ t1 u1) (Pi     _ t2 u2) = (&&) <$> term t1 t2 <*> term u1 u2
    termf (LocalVar i1)    (LocalVar i2)    = return (i1 == i2)
    termf _ _                               = return False

    ftermf :: FlatTermF (SharedTerm s) -> FlatTermF (SharedTerm s) -> IO Bool
    ftermf (Sort s) (Sort s') = return (s <= s')
    ftermf ftf1 ftf2 =
      case zipWithFlatTermF term ftf1 ftf2 of
        Nothing -> return False
        Just ftf3 -> Data.Foldable.and <$> sequenceA ftf3
