{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeFamilies #-}

{- |
Module      : SAWCore.SCTypeCheck
Copyright   : Galois, Inc. 2012-2015
License     : BSD3
Maintainer  : jhendrix@galois.com
Stability   : experimental
Portability : non-portable (language extensions)
-}

module SAWCore.SCTypeCheck
  ( TCError(..)
  , prettyTCError
  , throwTCError
  , TCM
  , runTCM
  , withErrorUTerm
  , atPos
  , LiftTCM(..)
  , inferTermF
  , inferFlatTermF
  , typeCheckWHNF
  , checkSubtype
  , ensureSortType
  , applyPiTyped
  , compileRecursor
  ) where

import Control.Applicative
import Control.Monad (forM_, mapM, unless, void)
import Control.Monad.Except (MonadError(..), ExceptT, runExceptT)
import Control.Monad.IO.Class (MonadIO(..))
import Control.Monad.Reader (MonadReader(..), ReaderT(..))

import qualified Data.IntMap as IntMap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Vector as V
import Prelude hiding (mapM, maximum)

import qualified SAWSupport.Pretty as PPS (defaultOpts, render)

import SAWCore.Module
  ( ctorName
  , dtName
  , lookupVarIndexInMap
  , Ctor(..)
  , DataType(..)
  , ResolvedName(..)
  )
import SAWCore.Name
import SAWCore.Parser.AST (UTerm, prettyUTerm)
import SAWCore.Parser.Position
import SAWCore.Recognizer
import SAWCore.SharedTerm
import SAWCore.Term.Certified (scRecordValue)
import SAWCore.Term.Functor
import SAWCore.Term.Pretty (ppTermPure)

-- | The 'ReaderT' environment for a type-checking computation.
type TCEnv = SharedContext

-- | The monad for type checking and inference, which:
--
-- * Maintains a 'SharedContext';
--
-- * Can throw 'TCError's
newtype TCM a = TCM (ReaderT TCEnv (ExceptT TCError IO) a)
  deriving (Functor, Applicative, Monad, MonadFail, MonadIO,
            MonadReader TCEnv, MonadError TCError)

-- | Run a type-checking computation in a given context, starting from the empty
-- memoization table
runTCM ::
  TCM a -> SharedContext -> IO (Either TCError a)
runTCM (TCM m) sc =
  runExceptT $ runReaderT m sc

-- | Augment and rethrow any 'TCError' thrown by the given computation.
rethrowTCError :: (MonadError TCError m) => (TCError -> TCError) -> m a -> m a
rethrowTCError f m = catchError m (throwError . f)

-- | Run a type-checking computation @m@ and tag any error it throws with the
-- 'ErrorUTerm' constructor
withErrorUTerm :: MonadError TCError m => UTerm -> m a -> m a
withErrorUTerm t = rethrowTCError (ErrorUTerm t)

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
    do sc <- ask
       liftIO (f sc)

instance LiftTCM b => LiftTCM (a -> b) where
  type TCMLifted (a -> b) = a -> TCMLifted b
  liftTCM f a = liftTCM (\sc -> f sc a)

-- | Errors that can occur during type-checking
data TCError
  = NotSort Term
  | NotFuncTypeInApp Term Term
  | NotTupleType Term
  | BadTupleIndex Int Term
  | NotRecordType Term
  | BadRecordField FieldName Term
  | UnboundName Text
  | SubtypeFailure Term Term
  | EmptyVectorLit
  | NoSuchDataType NameInfo
  | NoSuchConstant NameInfo
  | MalformedRecursor NameInfo Sort String
  | DeclError Text String
  | ErrorPos Pos TCError
  | ErrorUTerm UTerm TCError


-- | Throw a type-checking error
throwTCError :: (MonadError TCError m) => TCError -> m a
throwTCError e = throwError e

-- | Pretty-print a type-checking error
prettyTCError :: TCError -> [String]
prettyTCError e = helper Nothing e where

  ppWithPos :: Maybe Pos -> [String] -> [String]
  ppWithPos maybe_p strs =
    case maybe_p of
      Just p -> ppPos p : strs
      Nothing -> strs

  helper :: Maybe Pos -> TCError -> [String]
  helper mp err =
    case err of
      NotSort ty ->
        ppWithPos mp [ "Not a sort" , ishow ty ]
      NotFuncTypeInApp f arg ->
        ppWithPos mp [ "Function application with non-function type"
                     , "For term:"
                     , ishow f
                     , "With type:"
                     , tyshow f
                     , "To argument:"
                     , ishow arg ]
      NotTupleType ty ->
        ppWithPos mp [ "Tuple field projection with non-tuple type"
                     , ishow ty ]
      BadTupleIndex n ty ->
        ppWithPos mp [ "Bad tuple index (" ++ show n ++ ") for type"
                     , ishow ty ]
      NotRecordType t ->
        ppWithPos mp [ "Record field projection with non-record type"
                     , tyshow t
                     , "In term:"
                     , ishow t ]
      BadRecordField n ty ->
        ppWithPos mp [ "Bad record field (" ++ show n ++ ") for type"
                     , ishow ty ]
      UnboundName str ->
        ppWithPos mp [ "Unbound name: " ++ show str ]
      SubtypeFailure trm tp2 ->
        ppWithPos mp [ "Inferred type", tyshow trm,
                       "Not a subtype of expected type", ishow tp2,
                       "For term", ishow trm ]
      EmptyVectorLit ->
        ppWithPos mp [ "Empty vector literal"]
      NoSuchDataType d ->
        ppWithPos mp [ "No such data type: " ++ show d ]
      NoSuchConstant c ->
        ppWithPos mp [ "No such constant: " ++ show c ]
      MalformedRecursor d s reason ->
        ppWithPos mp [ "Malformed recursor"
                     , indent "  " (Text.unpack (toAbsoluteName d) ++ sortSuffix s)
                     , reason ]
      DeclError nm reason ->
        ppWithPos mp [ "Malformed declaration for " ++ show nm, reason ]
      ErrorPos p err' ->
        helper (Just p) err'
      ErrorUTerm t err' ->
        ppWithPos mp [ "While typechecking term:"
                     , indent "  " $ PPS.render PPS.defaultOpts (prettyUTerm t)
                     ]
        ++ helper mp err'

  -- | Add prefix to every line, but remove final trailing newline
  indent :: String -> String -> String
  indent prefix s = init (unlines (map (prefix ++) (lines s)))

  ishow :: Term -> String
  ishow tm = indent "  " $ ppTermPure PPS.defaultOpts tm

  tyshow :: Term -> String
  tyshow t =
    case termSortOrType t of
      Left s ->
        indent "  " $ show s
      Right tm ->
        indent "  " $ ppTermPure PPS.defaultOpts tm

  sortSuffix :: Sort -> String
  sortSuffix s =
    case s of
      TypeSort 0 -> "#rec"
      TypeSort n -> "#rec" ++ show n
      PropSort -> "#ind"

instance Show TCError where
  show = unlines . prettyTCError

-- | Construct a typed term from a 'TermF' where each subterm has
-- already been labeled with its type.
inferTermF :: TermF Term -> TCM Term
inferTermF tf =
  case tf of
    FTermF ftf ->
      inferFlatTermF ftf
    App t1 t2 ->
      do let err = NotFuncTypeInApp t1 t2
         ty1 <- liftTCM scTypeOf t1
         (_nm, arg_tp, _ret_tp) <- ensurePiType err ty1
         checkSubtype t2 arg_tp
         liftTCM scApply t1 t2
    Lambda x t1 t2 ->
      do void $ ensureSortType t1
         liftTCM scLambda x t1 t2
    Pi x t1 t2 ->
      do void $ ensureSortType t1
         void $ ensureSortType t2
         liftTCM scPi x t1 t2
    Constant nm ->
      do mm <- liftTCM scGetModuleMap
         case lookupVarIndexInMap (nameIndex nm) mm of
           Nothing -> throwTCError $ NoSuchConstant (nameInfo nm)
           Just _ -> liftTCM scConst nm
    Variable vn tp ->
      liftTCM scVariable vn tp

-- | Construct a typed term from a 'FlatTermF' where each subterm has
-- already been labeled with its type.
inferFlatTermF :: FlatTermF Term -> TCM Term
inferFlatTermF ftf =
  case ftf of
    UnitValue ->
      liftTCM scUnitValue
    UnitType ->
      liftTCM scUnitType
    PairValue t1 t2 ->
      liftTCM scPairValue t1 t2
    PairType t1 t2 ->
      do void $ ensureSortType t1
         void $ ensureSortType t2
         liftTCM scPairType t1 t2
    PairLeft t ->
      do void $ ensurePairType =<< liftTCM scTypeOf t
         liftTCM scPairLeft t
    PairRight t ->
      do void $ ensurePairType =<< liftTCM scTypeOf t
         liftTCM scPairRight t
    Recursor r ->
      do mm <- liftTCM scGetModuleMap
         let d = recursorDataType r
         let s = recursorSort r
         case lookupVarIndexInMap (nameIndex d) mm of
           Just (ResolvedDataType _dt) -> liftTCM scRecursor d s
           _ -> throwTCError $ NoSuchDataType (nameInfo d)
    RecordType elems ->
      do void $ mapM (ensureSortType . snd) elems
         liftTCM scRecordType elems
    RecordValue elems ->
      liftTCM scRecordValue elems
    RecordProj t fld ->
      do ty <- liftTCM scTypeOf t
         ts <- ensureRecordType (NotRecordType t) ty
         unless (Map.member fld ts) $
           throwTCError $ BadRecordField fld ty
         liftTCM scRecordSelect t fld
    Sort s flags ->
      liftTCM scSortWithFlags s flags
    ArrayValue tp vs ->
      do void $ ensureSortType tp
         tp' <- typeCheckWHNF tp
         forM_ vs $ \v_elem -> checkSubtype v_elem tp'
         liftTCM scVector tp (V.toList vs)
    StringLit s ->
      liftTCM scString s

-- | Check that @fun_tp=Pi x a b@ and that @arg@ has type @a@, and return the
-- result of substituting @arg@ for @x@ in the result type @b@, i.e.,
-- @[arg/x]b@.
-- If @fun_tp@ is not a pi type, raise the supplied error.
applyPiTyped :: TCError -> Term -> Term -> TCM Term
applyPiTyped err fun_tp arg =
  ensurePiType err fun_tp >>= \(nm, arg_tp, ret_tp) ->
  do checkSubtype arg arg_tp
     let sub = IntMap.singleton (vnIndex nm) arg
     liftTCM scInstantiate sub ret_tp

-- | Ensure that a 'Term' matches a recognizer function, normalizing if
-- necessary; otherwise throw the supplied 'TCError'
ensureRecognizer :: Recognizer Term a -> TCError -> Term -> TCM a
ensureRecognizer f _ (f -> Just a) = return a
ensureRecognizer f err trm =
  typeCheckWHNF trm >>= \case
  (f -> Just a) -> return a
  _ -> throwTCError err

-- | Ensure the type of a 'Term' is a sort, and return that sort.
ensureSortType :: Term -> TCM Sort
ensureSortType t = either pure ensureSort (termSortOrType t)

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

-- | Reduce a type to weak head-normal form (using 'scWhnf').
typeCheckWHNF :: Term -> TCM Term
typeCheckWHNF = liftTCM scWhnf

-- | Check that one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s.
checkSubtype :: Term -> Term -> TCM ()
checkSubtype arg req_tp =
  do arg_tp' <- liftTCM scWhnf =<< liftTCM scTypeOf arg
     req_tp' <- liftTCM scWhnf req_tp
     ok <- isSubtype arg_tp' req_tp'
     if ok then return () else throwTCError $ SubtypeFailure arg req_tp

-- | Check if one type is a subtype of another, assuming both arguments are
-- types, i.e., that both have type Sort s for some s, and that they are both
-- already in WHNF
isSubtype :: Term -> Term -> TCM Bool
isSubtype (unwrapTermF -> Pi x1 a1 b1) (unwrapTermF -> Pi x2 a2 b2)
  | x1 == x2 =
    (&&) <$> areConvertible a1 a2 <*> isSubtype b1 b2
  | otherwise =
    do conv1 <- areConvertible a1 a2
       var1 <- liftTCM scVariable x1 a1
       let sub = IntMap.singleton (vnIndex x2) var1
       b2' <- liftTCM scInstantiate sub b2
       conv2 <- isSubtype b1 b2'
       pure (conv1 && conv2)
isSubtype (asSort -> Just s1) (asSort -> Just s2) | s1 <= s2 = return True
isSubtype t1' t2' = areConvertible t1' t2'

-- | Check if two terms are "convertible for type-checking", meaning that they
-- are convertible up to the reductions performed by 'scWhnf'.
areConvertible :: Term -> Term -> TCM Bool
areConvertible t1 t2 = liftTCM scConvertibleEval scWhnf True t1 t2


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
           MalformedRecursor (nameInfo d) s
           "Disallowed propositional elimination"

     unless (allowedElimSort dt s) $ throwTCError err
     return crec
