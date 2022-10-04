{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DerivingStrategies #-}

{- |
Module      : SAWScript.Prover.MRSolver.Monad
Copyright   : Galois, Inc. 2022
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module defines the monad used by Mr. Solver ('MRM') as well as the core
monadic combinators for operating on terms.
-}

module SAWScript.Prover.MRSolver.Monad where

import Data.List (find, findIndex, foldl')
import qualified Data.Text as T
import System.IO (hPutStrLn, stderr)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import GHC.Generics

import Data.Map (Map)
import qualified Data.Map as Map

import Data.HashMap.Lazy (HashMap)
import qualified Data.HashMap.Lazy as HashMap

import Prettyprinter

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.CtxTerm (MonadTerm(..))
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Cryptol.Monadify

import SAWScript.Prover.MRSolver.Term


----------------------------------------------------------------------
-- * MR Solver Errors
----------------------------------------------------------------------

-- | The context in which a failure occurred
data FailCtx
  = FailCtxRefines NormComp NormComp
  | FailCtxCoIndHyp CoIndHyp
  | FailCtxMNF Term
  deriving Show

-- | That's MR. Failure to you
data MRFailure
  = TermsNotRel Bool Term Term
  | TypesNotRel Bool Type Type
  | CompsDoNotRefine NormComp NormComp
  | ReturnNotError Term
  | FunsNotEq FunName FunName
  | CannotLookupFunDef FunName
  | RecursiveUnfold FunName
  | MalformedLetRecTypes Term
  | MalformedDefsFun Term
  | MalformedComp Term
  | NotCompFunType Term
  | AssertionNotProvable Term
  | AssumptionNotProvable Term
  | InvariantNotProvable FunName FunName Term
    -- | A local variable binding
  | MRFailureLocalVar LocalName MRFailure
    -- | Information about the context of the failure
  | MRFailureCtx FailCtx MRFailure
    -- | Records a disjunctive branch we took, where both cases failed
  | MRFailureDisj MRFailure MRFailure
  deriving Show

pattern TermsNotEq :: Term -> Term -> MRFailure
pattern TermsNotEq t1 t2 = TermsNotRel False t1 t2

pattern TypesNotEq :: Type -> Type -> MRFailure
pattern TypesNotEq t1 t2 = TypesNotRel False t1 t2

-- | Remove the context from a 'MRFailure', i.e. remove all applications of the 
-- 'MRFailureLocalVar' and 'MRFailureCtx' constructors
mrFailureWithoutCtx :: MRFailure -> MRFailure
mrFailureWithoutCtx (MRFailureLocalVar x err) =
  MRFailureLocalVar x (mrFailureWithoutCtx err)
mrFailureWithoutCtx (MRFailureCtx _ err) = mrFailureWithoutCtx err
mrFailureWithoutCtx (MRFailureDisj err1 err2) =
  MRFailureDisj (mrFailureWithoutCtx err1) (mrFailureWithoutCtx err2)
mrFailureWithoutCtx err = err

-- | Pretty-print an object prefixed with a 'String' that describes it
ppWithPrefix :: PrettyInCtx a => String -> a -> PPInCtxM SawDoc
ppWithPrefix str a = (pretty str <>) <$> nest 2 <$> (line <>) <$> prettyInCtx a

-- | Pretty-print two objects, prefixed with a 'String' and with a separator
ppWithPrefixSep :: (PrettyInCtx a, PrettyInCtx b) =>
                   String -> a -> String -> b -> PPInCtxM SawDoc
ppWithPrefixSep d1 t2 d3 t4 =
  prettyInCtx t2 >>= \d2 -> prettyInCtx t4 >>= \d4 ->
  return $ group (pretty d1 <> nest 2 (line <> d2) <> line <>
                  pretty d3 <> nest 2 (line <> d4))

-- | Apply 'vsep' to a list of pretty-printing computations
vsepM :: [PPInCtxM SawDoc] -> PPInCtxM SawDoc
vsepM = fmap vsep . sequence

instance PrettyInCtx FailCtx where
  prettyInCtx (FailCtxRefines m1 m2) =
    group <$> nest 2 <$>
    ppWithPrefixSep "When proving refinement:" m1 "|=" m2
  prettyInCtx (FailCtxCoIndHyp hyp) =
    group <$> nest 2 <$>
    ppWithPrefix "When doing co-induction with hypothesis:" hyp
  prettyInCtx (FailCtxMNF t) =
    group <$> nest 2 <$> vsepM [return "When normalizing computation:",
                                prettyInCtx t]

instance PrettyInCtx MRFailure where
  prettyInCtx (TermsNotRel False t1 t2) =
    ppWithPrefixSep "Could not prove terms equal:" t1 "and" t2
  prettyInCtx (TermsNotRel True t1 t2) =
    ppWithPrefixSep "Could not prove terms heterogeneously related:" t1 "and" t2
  prettyInCtx (TypesNotRel False tp1 tp2) =
    ppWithPrefixSep "Types not equal:" tp1 "and" tp2
  prettyInCtx (TypesNotRel True tp1 tp2) =
    ppWithPrefixSep "Types not heterogeneously related:" tp1 "and" tp2
  prettyInCtx (CompsDoNotRefine m1 m2) =
    ppWithPrefixSep "Could not prove refinement: " m1 "|=" m2
  prettyInCtx (ReturnNotError t) =
    ppWithPrefix "errorM computation not equal to:" (ReturnM t)
  prettyInCtx (FunsNotEq nm1 nm2) =
    vsepM [return "Named functions not equal:",
           prettyInCtx nm1, prettyInCtx nm2]
  prettyInCtx (CannotLookupFunDef nm) =
    ppWithPrefix "Could not find definition for function:" nm
  prettyInCtx (RecursiveUnfold nm) =
    ppWithPrefix "Recursive unfolding of function inside its own body:" nm
  prettyInCtx (MalformedLetRecTypes t) =
    ppWithPrefix "Not a ground LetRecTypes list:" t
  prettyInCtx (MalformedDefsFun t) =
    ppWithPrefix "Cannot handle letRecM recursive definitions term:" t
  prettyInCtx (MalformedComp t) =
    ppWithPrefix "Could not handle computation:" t
  prettyInCtx (NotCompFunType tp) =
    ppWithPrefix "Not a computation or computational function type:" tp
  prettyInCtx (AssertionNotProvable cond) =
    ppWithPrefix "Failed to prove assertion:" cond
  prettyInCtx (AssumptionNotProvable cond) =
    ppWithPrefix "Failed to prove condition for `assuming`:" cond
  prettyInCtx (InvariantNotProvable f g pre) =
    prettyAppList [return "Could not prove loop invariant for functions",
                   prettyInCtx f, return "and", prettyInCtx g,
                   return ":", prettyInCtx pre]
  prettyInCtx (MRFailureLocalVar x err) =
    local (x:) $ prettyInCtx err
  prettyInCtx (MRFailureCtx ctx err) =
    do pp1 <- prettyInCtx ctx
       pp2 <- prettyInCtx err
       return (pp1 <> line <> pp2)
  prettyInCtx (MRFailureDisj err1 err2) =
    ppWithPrefixSep "Tried two comparisons:" err1 "Backtracking..." err2

-- | Render a 'MRFailure' to a 'String'
showMRFailure :: MRFailure -> String
showMRFailure = showInCtx emptyMRVarCtx

-- | Render a 'MRFailure' to a 'String' without its context (see
-- 'mrFailureWithoutCtx')
showMRFailureNoCtx :: MRFailure -> String
showMRFailureNoCtx = showMRFailure . mrFailureWithoutCtx


----------------------------------------------------------------------
-- * MR Monad
----------------------------------------------------------------------

-- | Classification info for what sort of variable an 'MRVar' is
data MRVarInfo
     -- | An existential variable, that might be instantiated
  = EVarInfo (Maybe Term)
    -- | A letrec-bound function, with its body
  | FunVarInfo Term

-- | A map from 'MRVar's to their info
type MRVarMap = Map MRVar MRVarInfo

-- | Test if a 'Term' is an application of an 'ExtCns' to some arguments
asExtCnsApp :: Recognizer Term (ExtCns Term, [Term])
asExtCnsApp (asApplyAll -> (asExtCns -> Just ec, args)) =
  return (ec, args)
asExtCnsApp _ = Nothing

-- | Recognize an evar applied to 0 or more arguments relative to a 'MRVarMap'
-- along with its instantiation, if any
asEVarApp :: MRVarMap -> Recognizer Term (MRVar, [Term], Maybe Term)
asEVarApp var_map (asExtCnsApp -> Just (ec, args))
  | Just (EVarInfo maybe_inst) <- Map.lookup (MRVar ec) var_map =
    Just (MRVar ec, args, maybe_inst)
asEVarApp _ _ = Nothing

-- | A co-inductive hypothesis of the form:
--
-- > forall x1, ..., xn. F y1 ... ym |= G z1 ... zl
--
-- for some universal context @x1:T1, ..., xn:Tn@ and some lists of argument
-- expressions @y1, ..., ym@ and @z1, ..., zl@ over the universal context.
data CoIndHyp = CoIndHyp {
  -- | The uvars that were in scope when this assmption was created
  coIndHypCtx :: MRVarCtx,
  -- | The LHS function name
  coIndHypLHSFun :: FunName,
  -- | The RHS function name
  coIndHypRHSFun :: FunName,
  -- | The LHS argument expressions @y1, ..., ym@ over the 'coIndHypCtx' uvars
  coIndHypLHS :: [Term],
  -- | The RHS argument expressions @y1, ..., ym@ over the 'coIndHypCtx' uvars
  coIndHypRHS :: [Term],
  -- | The invariant for the left-hand arguments, as a closed function from
  -- the left-hand arguments to @Bool@
  coIndHypInvariantLHS :: Maybe Term,
  -- | The invariant for the right-hand arguments, as a closed function from
  -- the left-hand arguments to @Bool@
  coIndHypInvariantRHS :: Maybe Term
} deriving Show

-- | Extract the @i@th argument on either the left- or right-hand side of a
-- coinductive hypothesis
coIndHypArg :: CoIndHyp -> Either Int Int -> Term
coIndHypArg hyp (Left i) = (coIndHypLHS hyp) !! i
coIndHypArg hyp (Right i) = (coIndHypRHS hyp) !! i

-- | Set the @i@th argument on either the left- or right-hand side of a
-- coinductive hypothesis to the given value
coIndHypSetArg :: CoIndHyp -> Either Int Int -> Term -> CoIndHyp
coIndHypSetArg hyp@(CoIndHyp {..}) (Left i) x =
  hyp { coIndHypLHS = take i coIndHypLHS ++ x : drop (i+1) coIndHypLHS }
coIndHypSetArg hyp@(CoIndHyp {..}) (Right i) x =
  hyp { coIndHypRHS = take i coIndHypRHS ++ x : drop (i+1) coIndHypRHS }

-- | Add a variable to the context of a coinductive hypothesis, returning the
-- updated coinductive hypothesis and a 'Term' which is the new variable
coIndHypWithVar :: CoIndHyp -> LocalName -> Type -> MRM (CoIndHyp, Term)
coIndHypWithVar (CoIndHyp ctx f1 f2 args1 args2 invar1 invar2) nm tp =
  do var <- liftSC1 scLocalVar 0
     let ctx' = mrVarCtxAppend (singletonMRVarCtx nm tp) ctx
     (args1', args2') <- liftTermLike 0 1 (args1, args2)
     return (CoIndHyp ctx' f1 f2 args1' args2' invar1 invar2, var)
  
-- | A map from pairs of function names to co-inductive hypotheses over those
-- names
type CoIndHyps = Map (FunName, FunName) CoIndHyp

instance PrettyInCtx CoIndHyp where
  prettyInCtx (CoIndHyp ctx f1 f2 args1 args2 invar1 invar2) =
    -- ignore whatever context we're in and use `ctx` instead
    return $ flip runPPInCtxM ctx $
    prettyAppList [prettyInCtx ctx, return ".",
                   (case invar1 of
                       Just f -> prettyTermApp f args1
                       Nothing -> return "True"), return "=>",
                   (case invar2 of
                       Just f -> prettyTermApp f args2
                       Nothing -> return "True"), return "=>",
                   prettyTermApp (funNameTerm f1) args1,
                   return "|=",
                   prettyTermApp (funNameTerm f2) args2]

-- | An assumption that something is equal to one of the constructors of a
-- datatype, e.g. equal to @Left@ of some 'Term' or @Right@ of some 'Term'
data DataTypeAssump
  = IsLeft Term | IsRight Term | IsNum Term | IsInf
  deriving (Generic, Show, TermLike)

instance PrettyInCtx DataTypeAssump where
  prettyInCtx (IsLeft  x) = prettyInCtx x >>= ppWithPrefix "Left _ _" 
  prettyInCtx (IsRight x) = prettyInCtx x >>= ppWithPrefix "Right _ _"
  prettyInCtx (IsNum   x) = prettyInCtx x >>= ppWithPrefix "TCNum"
  prettyInCtx IsInf = return "TCInf"

-- | A map from 'Term's to 'DataTypeAssump's over that term
type DataTypeAssumps = HashMap Term DataTypeAssump

-- | Parameters and locals for MR. Solver
data MRInfo = MRInfo {
  -- | Global shared context for building terms, etc.
  mriSC :: SharedContext,
  -- | SMT timeout for SMT calls made by Mr. Solver
  mriSMTTimeout :: Maybe Integer,
  -- | The current context of universal variables
  mriUVars :: MRVarCtx,
  -- | The top-level Mr Solver environment
  mriEnv :: MREnv,
  -- | The current set of co-inductive hypotheses
  mriCoIndHyps :: CoIndHyps,
  -- | The current assumptions, which are conjoined into a single Boolean term;
  -- note that these have the current UVars free
  mriAssumptions :: Term,
  -- | The current set of 'DataTypeAssump's
  mriDataTypeAssumps :: DataTypeAssumps
}

-- | State maintained by MR. Solver
data MRState = MRState {
  -- | The existential and letrec-bound variables
  mrsVars :: MRVarMap
}

-- | The exception type for MR. Solver, which is either a 'MRFailure' or a
-- widening request
data MRExn = MRExnFailure MRFailure
           | MRExnWiden FunName FunName [Either Int Int]
           deriving Show

-- | Mr. Monad, the monad used by MR. Solver, which has 'MRInfo' as as a
-- shared environment, 'MRState' as state, and 'MRFailure' as an exception
-- type, all over an 'IO' monad
newtype MRM a = MRM { unMRM :: ReaderT MRInfo (StateT MRState
                                              (ExceptT MRExn IO)) a }
              deriving newtype (Functor, Applicative, Monad, MonadIO,
                                MonadReader MRInfo, MonadState MRState,
                                                    MonadError MRExn)

instance MonadTerm MRM where
  mkTermF = liftSC1 scTermF
  liftTerm = liftSC3 incVars
  whnfTerm = liftSC1 scWhnf
  substTerm = liftSC3 instantiateVarList

-- | Get the current value of 'mriSC'
mrSC :: MRM SharedContext
mrSC = mriSC <$> ask

-- | Get the current value of 'mriSMTTimeout'
mrSMTTimeout :: MRM (Maybe Integer)
mrSMTTimeout = mriSMTTimeout <$> ask

-- | Get the current value of 'mriUVars'
mrUVars :: MRM MRVarCtx
mrUVars = mriUVars <$> ask

-- | Get the current function assumptions
mrFunAssumps :: MRM FunAssumps
mrFunAssumps = mreFunAssumps <$> mriEnv <$> ask

-- | Get the current value of 'mriCoIndHyps'
mrCoIndHyps :: MRM CoIndHyps
mrCoIndHyps = mriCoIndHyps <$> ask

-- | Get the current value of 'mriAssumptions'
mrAssumptions :: MRM Term
mrAssumptions = mriAssumptions <$> ask

-- | Get the current value of 'mriDataTypeAssumps'
mrDataTypeAssumps :: MRM DataTypeAssumps
mrDataTypeAssumps = mriDataTypeAssumps <$> ask

-- | Get the current debug level
mrDebugLevel :: MRM Int
mrDebugLevel = mreDebugLevel <$> mriEnv <$> ask

-- | Get the current value of 'mriEnv'
mrEnv :: MRM MREnv
mrEnv = mriEnv <$> ask

-- | Get the current value of 'mrsVars'
mrVars :: MRM MRVarMap
mrVars = mrsVars <$> get

-- | Run an 'MRM' computation and return a result or an error
runMRM :: SharedContext -> Maybe Integer -> MREnv ->
          MRM a -> IO (Either MRFailure a)
runMRM sc timeout env m =
  do true_tm <- scBool sc True
     let init_info = MRInfo { mriSC = sc, mriSMTTimeout = timeout,
                              mriEnv = env,
                              mriUVars = emptyMRVarCtx,
                              mriCoIndHyps = Map.empty,
                              mriAssumptions = true_tm,
                              mriDataTypeAssumps = HashMap.empty }
     let init_st = MRState { mrsVars = Map.empty }
     res <- runExceptT $ flip evalStateT init_st $
       flip runReaderT init_info $ unMRM m
     case res of
       Right a -> return $ Right a
       Left (MRExnFailure failure) -> return $ Left failure
       Left exn -> fail ("runMRM: unexpected internal exception: " ++ show exn)

-- | Throw an 'MRFailure'
throwMRFailure :: MRFailure -> MRM a
throwMRFailure = throwError . MRExnFailure

-- | Apply a function to any failure thrown by an 'MRM' computation
mapMRFailure :: (MRFailure -> MRFailure) -> MRM a -> MRM a
mapMRFailure f m = catchError m $ \case
  MRExnFailure failure -> throwError $ MRExnFailure $ f failure
  e -> throwError e

-- | Catch any 'MRFailure' raised by a computation
catchFailure :: MRM a -> (MRFailure -> MRM a) -> MRM a
catchFailure m f =
  m `catchError` \case
  MRExnFailure failure -> f failure
  e -> throwError e

-- | Try two different 'MRM' computations, combining their failures if needed.
-- Note that the 'MRState' will reset if the first computation fails.
mrOr :: MRM a -> MRM a -> MRM a
mrOr m1 m2 =
  catchFailure m1 $ \err1 ->
  catchFailure m2 $ \err2 ->
  throwMRFailure $ MRFailureDisj err1 err2

-- | Run an 'MRM' computation in an extended failure context
withFailureCtx :: FailCtx -> MRM a -> MRM a
withFailureCtx ctx = mapMRFailure (MRFailureCtx ctx)

{-
-- | Catch any errors thrown by a computation and coerce them to a 'Left'
catchErrorEither :: MonadError e m => m a -> m (Either e a)
catchErrorEither m = catchError (Right <$> m) (return . Left)
-}

-- FIXME: replace these individual lifting functions with a more general
-- typeclass like LiftTCM

-- | Lift a nullary SharedTerm computation into 'MRM'
liftSC0 :: (SharedContext -> IO a) -> MRM a
liftSC0 f = mrSC >>= \sc -> liftIO (f sc)

-- | Lift a unary SharedTerm computation into 'MRM'
liftSC1 :: (SharedContext -> a -> IO b) -> a -> MRM b
liftSC1 f a = mrSC >>= \sc -> liftIO (f sc a)

-- | Lift a binary SharedTerm computation into 'MRM'
liftSC2 :: (SharedContext -> a -> b -> IO c) -> a -> b -> MRM c
liftSC2 f a b = mrSC >>= \sc -> liftIO (f sc a b)

-- | Lift a ternary SharedTerm computation into 'MRM'
liftSC3 :: (SharedContext -> a -> b -> c -> IO d) -> a -> b -> c -> MRM d
liftSC3 f a b c = mrSC >>= \sc -> liftIO (f sc a b c)

-- | Lift a quaternary SharedTerm computation into 'MRM'
liftSC4 :: (SharedContext -> a -> b -> c -> d -> IO e) -> a -> b -> c -> d ->
           MRM e
liftSC4 f a b c d = mrSC >>= \sc -> liftIO (f sc a b c d)

-- | Lift a quinary SharedTerm computation into 'MRM'
liftSC5 :: (SharedContext -> a -> b -> c -> d -> e -> IO f) ->
           a -> b -> c -> d -> e -> MRM f
liftSC5 f a b c d e = mrSC >>= \sc -> liftIO (f sc a b c d e)


----------------------------------------------------------------------
-- * Functions for Building Terms
----------------------------------------------------------------------

-- | Create a term representing the type @IsFinite n@
mrIsFinite :: Term -> MRM Term
mrIsFinite n = liftSC2 scGlobalApply "CryptolM.isFinite" [n]

-- | Create a term representing an application of @Prelude.error@
mrErrorTerm :: Term -> T.Text -> MRM Term
mrErrorTerm a str =
  do err_str <- liftSC1 scString str
     liftSC2 scGlobalApply "Prelude.error" [a, err_str]

-- | Create a term representing an application of @Prelude.genBVVecFromVec@,
-- where the default value argument is @Prelude.error@ of the given 'T.Text' 
mrGenBVVecFromVec :: Term -> Term -> Term -> T.Text -> Term -> Term -> MRM Term
mrGenBVVecFromVec m a v def_err_str n len =
  do err_tm <- mrErrorTerm a def_err_str
     liftSC2 scGlobalApply "Prelude.genBVVecFromVec" [m, a, v, err_tm, n, len]

-- | Create a term representing an application of @Prelude.genFromBVVec@,
-- where the default value argument is @Prelude.error@ of the given 'T.Text' 
mrGenFromBVVec :: Term -> Term -> Term -> Term -> T.Text -> Term -> MRM Term
mrGenFromBVVec n len a v def_err_str m =
  do err_tm <- mrErrorTerm a def_err_str
     liftSC2 scGlobalApply "Prelude.genFromBVVec" [n, len, a, v, err_tm, m]


----------------------------------------------------------------------
-- * Monadic Operations on Terms
----------------------------------------------------------------------

-- | Apply a 'TermProj' to perform a projection on a 'Term'
doTermProj :: Term -> TermProj -> MRM Term
doTermProj (asPairValue -> Just (t, _)) TermProjLeft = return t
doTermProj (asPairValue -> Just (_, t)) TermProjRight = return t
doTermProj (asRecordValue -> Just t_map) (TermProjRecord fld)
  | Just t <- Map.lookup fld t_map = return t
doTermProj t TermProjLeft = liftSC1 scPairLeft t
doTermProj t TermProjRight = liftSC1 scPairRight t
doTermProj t (TermProjRecord fld) = liftSC2 scRecordSelect t fld

-- | Apply a 'TermProj' to a type to get the output type of the projection,
-- assuming that the type is already normalized
doTypeProj :: Term -> TermProj -> MRM Term
doTypeProj (asPairType -> Just (tp1, _)) TermProjLeft = return tp1
doTypeProj (asPairType -> Just (_, tp2)) TermProjRight = return tp2
doTypeProj (asRecordType -> Just tp_map) (TermProjRecord fld)
  | Just tp <- Map.lookup fld tp_map
  = return tp
doTypeProj _ _ =
  -- FIXME: better error message? This is an error and not an MRFailure because
  -- we should only be projecting types for terms that we have already seen...
  error "doTypeProj"

-- | Get and normalize the type of a 'FunName'
funNameType :: FunName -> MRM Term
funNameType (LetRecName var) = liftSC1 scWhnf $ mrVarType var
funNameType (EVarFunName var) = liftSC1 scWhnf $ mrVarType var
funNameType (GlobalName gd projs) =
  liftSC1 scWhnf (globalDefType gd) >>= \gd_tp ->
  foldM doTypeProj gd_tp projs

-- | Apply a 'Term' to a list of arguments and beta-reduce in Mr. Monad
mrApplyAll :: Term -> [Term] -> MRM Term
mrApplyAll f args = liftSC2 scApplyAllBeta f args

-- | Apply a 'Term' to a single argument and beta-reduce in Mr. Monad
mrApply :: Term -> Term -> MRM Term
mrApply f arg = mrApplyAll f [arg]

-- | Build a constructor application in Mr. Monad
mrCtorApp :: Ident -> [Term] -> MRM Term
mrCtorApp = liftSC2 scCtorApp

-- | Build a 'Term' for a global in Mr. Monad
mrGlobalTerm :: Ident -> MRM Term
mrGlobalTerm = liftSC1 scGlobalDef

-- | Like 'scBvConst', but if given a bitvector literal it is converted to a
-- natural number literal
mrBvToNat :: Term -> Term -> MRM Term
mrBvToNat _ (asArrayValue -> Just (asBoolType -> Just _,
                                   mapM asBool -> Just bits)) =
  liftSC1 scNat $ foldl' (\n bit -> if bit then 2*n+1 else 2*n) 0 bits
mrBvToNat n len = liftSC2 scGlobalApply "Prelude.bvToNat" [n, len]

-- | Get the current context of uvars as a list of variable names and their
-- types as SAW core 'Term's, with the least recently bound uvar first, i.e., in
-- the order as seen "from the outside"
mrUVarsOuterToInner :: MRM [(LocalName,Term)]
mrUVarsOuterToInner = mrVarCtxOuterToInner <$> mrUVars

-- | Get the current context of uvars as a list of variable names and their
-- types as SAW core 'Term's, with the most recently bound uvar first, i.e., in
-- the order as seen "from the inside"
mrUVarsInnerToOuter :: MRM [(LocalName,Term)]
mrUVarsInnerToOuter = mrVarCtxInnerToOuter <$> mrUVars

-- | Get the type of a 'Term' in the current uvar context
mrTypeOf :: Term -> MRM Term
mrTypeOf t =
  -- NOTE: scTypeOf' wants the type context in the most recently bound var first
  -- mrDebugPPPrefix 3 "mrTypeOf:" t >>
  mrUVarsInnerToOuter >>= \ctx -> liftSC2 scTypeOf' (map snd ctx) t

-- | Check if two 'Term's are convertible in the 'MRM' monad
mrConvertible :: Term -> Term -> MRM Bool
mrConvertible = liftSC4 scConvertibleEval scTypeCheckWHNF True

-- | Take a 'FunName' @f@ for a monadic function of type @vars -> CompM a@ and
-- compute the type @CompM [args/vars]a@ of @f@ applied to @args@. Return the
-- type @[args/vars]a@ that @CompM@ is applied to.
mrFunOutType :: FunName -> [Term] -> MRM Term
mrFunOutType fname args =
  mrApplyAll (funNameTerm fname) args >>= mrTypeOf >>= \case
    (asCompM -> Just tp) -> liftSC1 scWhnf tp
    _ -> do pp_ftype <- funNameType fname >>= mrPPInCtx
            pp_fname <- mrPPInCtx fname
            debugPrint 0 "mrFunOutType: function does not have CompM return type"
            debugPretty 0 ("Function:" <> pp_fname <> " with type: " <> pp_ftype)
            error "mrFunOutType"

-- | Turn a 'LocalName' into one not in a list, adding a suffix if necessary
uniquifyName :: LocalName -> [LocalName] -> LocalName
uniquifyName nm nms | notElem nm nms = nm
uniquifyName nm nms =
  case find (flip notElem nms) $
       map (T.append nm . T.pack . show) [(0::Int) ..] of
    Just nm' -> nm'
    Nothing -> error "uniquifyName"

-- | Turn a list of 'LocalName's into one names not in a list, adding suffixes
-- if necessary
uniquifyNames :: [LocalName] -> [LocalName] -> [LocalName]
uniquifyNames [] _ = []
uniquifyNames (nm:nms) nms_other =
  let nm' = uniquifyName nm nms_other in
  nm' : uniquifyNames nms (nm' : nms_other)

-- | Build a lambda term with the lifting (in the sense of 'incVars') of an
-- MR Solver term
mrLambdaLift :: TermLike tm => [(LocalName,Term)] -> tm ->
                ([Term] -> tm -> MRM Term) -> MRM Term
mrLambdaLift [] t f = f [] t
mrLambdaLift ctx t f =
  do -- uniquifyNames doesn't care about the order of the names in its second,
     -- argument, thus either inner-to-outer or outer-to-inner would work
     nms <- uniquifyNames (map fst ctx) <$> map fst <$> mrUVarsInnerToOuter
     let ctx' = zipWith (\nm (_,tp) -> (nm,tp)) nms ctx
     vars <- reverse <$> mapM (liftSC1 scLocalVar) [0 .. length ctx - 1]
     t' <- liftTermLike 0 (length ctx) t
     f vars t' >>= liftSC2 scLambdaList ctx'

-- | Run a MR Solver computation in a context extended with a universal
-- variable, which is passed as a 'Term' to the sub-computation. Note that any
-- assumptions made in the sub-computation will be lost when it completes.
withUVar :: LocalName -> Type -> (Term -> MRM a) -> MRM a
withUVar nm tp m = withUVars (singletonMRVarCtx nm tp) (\[v] -> m v)

-- | Run a MR Solver computation in a context extended with a universal variable
-- and pass it the lifting (in the sense of 'incVars') of an MR Solver term
withUVarLift :: TermLike tm => LocalName -> Type -> tm ->
                (Term -> tm -> MRM a) -> MRM a
withUVarLift nm tp t m =
  withUVar nm tp (\x -> liftTermLike 0 1 t >>= m x)

-- | Run a MR Solver computation in a context extended with a list of universal
-- variables, passing 'Term's for those variables to the supplied computation.
withUVars :: MRVarCtx -> ([Term] -> MRM a) -> MRM a
withUVars (mrVarCtxLength -> 0) f = f []
withUVars ctx f =
  do -- for uniquifyNames, we want to consider the oldest names first, thus we
     -- must pass the first argument in outer-to-inner order. uniquifyNames
     -- doesn't care about the order of the names in its second, argument, thus
     -- either inner-to-outer or outer-to-inner would work
     let ctx_l = mrVarCtxOuterToInner ctx
     nms <- uniquifyNames (map fst ctx_l) <$> map fst <$> mrUVarsInnerToOuter
     let ctx_u = mrVarCtxFromOuterToInner $ zip nms $ map snd ctx_l
     -- lift all the variables in our assumptions by the number of new uvars
     -- we're adding (we do not have to lift the types in our uvar context
     -- itself, since each type is in the context of all older uvars - see the
     -- definition of MRVarCtx)
     assumps' <- mrAssumptions >>= liftTerm 0 (mrVarCtxLength ctx)
     dataTypeAssumps' <- mrDataTypeAssumps >>= mapM (liftTermLike 0 (mrVarCtxLength ctx))
     -- make terms for our new uvars, extend the context, and continue
     vars <- reverse <$> mapM (liftSC1 scLocalVar) [0 .. mrVarCtxLength ctx - 1]
     local (\info -> info { mriUVars = mrVarCtxAppend ctx_u (mriUVars info),
                            mriAssumptions = assumps',
                            mriDataTypeAssumps = dataTypeAssumps' }) $
       mrDebugPPPrefix 3 "withUVars:" ctx_u >>
       foldr (\nm m -> mapMRFailure (MRFailureLocalVar nm) m) (f vars) nms

-- | Run a MR Solver in a top-level context, i.e., with no uvars or assumptions
withNoUVars :: MRM a -> MRM a
withNoUVars m =
  do true_tm <- liftSC1 scBool True
     local (\info -> info { mriUVars = emptyMRVarCtx, mriAssumptions = true_tm,
                            mriDataTypeAssumps = HashMap.empty }) m

-- | Run a MR Solver in a context of only the specified UVars, no others -
-- note that this also clears all assumptions
withOnlyUVars :: MRVarCtx -> MRM a -> MRM a
withOnlyUVars vars m = withNoUVars $ withUVars vars $ const m

-- | Build 'Term's for all the uvars currently in scope, ordered from least to
-- most recently bound
getAllUVarTerms :: MRM [Term]
getAllUVarTerms =
  (mrVarCtxLength <$> mrUVars) >>= \len ->
  mapM (liftSC1 scLocalVar) [len-1, len-2 .. 0]

-- | Lambda-abstract all the current uvars out of a 'Term', with the least
-- recently bound variable being abstracted first
lambdaUVarsM :: Term -> MRM Term
lambdaUVarsM t = mrUVarsOuterToInner >>= \ctx -> liftSC2 scLambdaList ctx t

-- | Pi-abstract all the current uvars out of a 'Term', with the least recently
-- bound variable being abstracted first
piUVarsM :: Term -> MRM Term
piUVarsM t = mrUVarsOuterToInner >>= \ctx -> liftSC2 scPiList ctx t

-- | Instantiate all uvars in a term using the supplied function
instantiateUVarsM :: TermLike a => (LocalName -> Term -> MRM Term) -> a -> MRM a
instantiateUVarsM f a =
  do ctx <- mrUVarsOuterToInner
     -- Remember: the uvar context is outermost to innermost, so we bind
     -- variables from left to right, substituting earlier ones into the types
     -- of later ones, but all substitutions are in reverse order, since
     -- substTerm and friends like innermost bindings first
     let helper :: [Term] -> [(LocalName,Term)] -> MRM [Term]
         helper tms [] = return tms
         helper tms ((nm,tp):vars) =
           do tp' <- substTerm 0 tms tp
              tm <- f nm tp'
              helper (tm:tms) vars
     ecs <- helper [] ctx
     substTermLike 0 ecs a

-- | Convert an 'MRVar' to a 'Term', applying it to all the uvars in scope
mrVarTerm :: MRVar -> MRM Term
mrVarTerm (MRVar ec) =
  do var_tm <- liftSC1 scExtCns ec
     vars <- getAllUVarTerms
     liftSC2 scApplyAll var_tm vars

-- | Create a dummy proof term of the specified type, which can be open but
-- should be of @Prop@ sort, by creating an 'ExtCns' axiom. This is sound as
-- long as we only use the resulting term in computation branches where we know
-- the proposition holds.
mrDummyProof :: Term -> MRM Term
mrDummyProof tp = piUVarsM tp >>= mrFreshVar "pf" >>= mrVarTerm

-- | Get the 'VarInfo' associated with a 'MRVar'
mrVarInfo :: MRVar -> MRM (Maybe MRVarInfo)
mrVarInfo var = Map.lookup var <$> mrVars

-- | Convert an 'ExtCns' to a 'FunName'
extCnsToFunName :: ExtCns Term -> MRM FunName
extCnsToFunName ec = let var = MRVar ec in mrVarInfo var >>= \case
  Just (EVarInfo _) -> return $ EVarFunName var
  Just (FunVarInfo _) -> return $ LetRecName var
  Nothing
    | Just glob <- asTypedGlobalDef (Unshared $ FTermF $ ExtCns ec) ->
      return $ GlobalName glob []
  _ -> error "extCnsToFunName: unreachable"

-- | Get the 'FunName' of a global definition
mrGlobalDef :: Ident -> MRM FunName
mrGlobalDef ident = asTypedGlobalDef <$> liftSC1 scGlobalDef ident >>= \case
  Just glob -> return $ GlobalName glob []
  _ -> error $ "mrGlobalDef: could not get GlobalDef of: " ++ show ident

-- | Get the body of a global definition, raising an 'error' if none is found
mrGlobalDefBody :: Ident -> MRM Term
mrGlobalDefBody ident = asConstant <$> liftSC1 scGlobalDef ident >>= \case
  Just (_, Just body) -> return body
  _ -> error $ "mrGlobalDefBody: global has no definition: " ++ show ident

-- | Get the body of a function @f@ if it has one
mrFunNameBody :: FunName -> MRM (Maybe Term)
mrFunNameBody (LetRecName var) =
  mrVarInfo var >>= \case
  Just (FunVarInfo body) -> return $ Just body
  _ -> error "mrFunBody: unknown letrec var"
mrFunNameBody (GlobalName glob projs)
  | Just body <- globalDefBody glob
  = Just <$> foldM doTermProj body projs
mrFunNameBody (GlobalName _ _) = return Nothing
mrFunNameBody (EVarFunName _) = return Nothing

-- | Get the body of a function @f@ applied to some arguments, if possible
mrFunBody :: FunName -> [Term] -> MRM (Maybe Term)
mrFunBody f args = mrFunNameBody f >>= \case
  Just body -> Just <$> mrApplyAll body args
  Nothing -> return Nothing

-- | Get the body of a function @f@ applied to some arguments, as per
-- 'mrFunBody', and also return whether its body recursively calls itself, as
-- per 'mrCallsFun'
mrFunBodyRecInfo :: FunName -> [Term] -> MRM (Maybe (Term, Bool))
mrFunBodyRecInfo f args =
  mrFunBody f args >>= \case
  Just f_body -> Just <$> (f_body,) <$> mrCallsFun f f_body
  Nothing -> return Nothing

-- | Test if a 'Term' contains, after possibly unfolding some functions, a call
-- to a given function @f@ again
mrCallsFun :: FunName -> Term -> MRM Bool
mrCallsFun f = memoFixTermFun $ \recurse t -> case t of
  (asExtCns -> Just ec) ->
    do g <- extCnsToFunName ec
       maybe_body <- mrFunNameBody g
       case maybe_body of
         _ | f == g -> return True
         Just body -> recurse body
         Nothing -> return False
  (asTypedGlobalProj -> Just (gdef, projs)) ->
    case globalDefBody gdef of
      _ | f == GlobalName gdef projs -> return True
      Just body -> recurse body
      Nothing -> return False
  (unwrapTermF -> tf) ->
    foldM (\b t' -> if b then return b else recurse t') False tf


----------------------------------------------------------------------
-- * Monadic Operations on Mr. Solver State
----------------------------------------------------------------------

-- | Make a fresh 'MRVar' of a given type, which must be closed, i.e., have no
-- free uvars
mrFreshVar :: LocalName -> Term -> MRM MRVar
mrFreshVar nm tp = MRVar <$> liftSC2 scFreshEC nm tp

-- | Set the info associated with an 'MRVar', assuming it has not been set
mrSetVarInfo :: MRVar -> MRVarInfo -> MRM ()
mrSetVarInfo var info =
  modify $ \st ->
  st { mrsVars =
         Map.alter (\case
                       Just _ -> error "mrSetVarInfo"
                       Nothing -> Just info)
         var (mrsVars st) }

-- | Make a fresh existential variable of the given type, abstracting out all
-- the current uvars and returning the new evar applied to all current uvars
mrFreshEVar :: LocalName -> Type -> MRM Term
mrFreshEVar nm (Type tp) =
  do tp' <- piUVarsM tp
     var <- mrFreshVar nm tp'
     mrSetVarInfo var (EVarInfo Nothing)
     mrVarTerm var

-- | Return a fresh sequence of existential variables from a 'MRVarCtx'.
-- Return the new evars all applied to the current uvars.
mrFreshEVars :: MRVarCtx -> MRM [Term]
mrFreshEVars = helper [] . mrVarCtxOuterToInner where
  -- Return fresh evars for the suffix of a context of variable names and types,
  -- where the supplied Terms are evars that have already been generated for the
  -- earlier part of the context, and so must be substituted into the remaining
  -- types in the context. Since we want to make fresh evars for the oldest
  -- variables first, the second argument must be in outer-to-inner order.
  helper :: [Term] -> [(LocalName,Term)] -> MRM [Term]
  helper evars [] = return evars
  helper evars ((nm,tp):ctx) =
    do evar <- substTerm 0 evars tp >>= mrFreshEVar nm . Type
       helper (evar:evars) ctx

-- | Set the value of an evar to a closed term
mrSetEVarClosed :: MRVar -> Term -> MRM ()
mrSetEVarClosed var val =
  do val_tp <- mrTypeOf val
     -- NOTE: need to instantiate any evars in the type of var, to ensure the
     -- following subtyping check will succeed
     var_tp <- mrSubstEVars $ mrVarType var
     -- FIXME: catch subtyping errors and report them as being evar failures
     eith_err <-
       liftSC2 (runTCM $ checkSubtype (TypedTerm val val_tp) var_tp) Nothing []
     case eith_err of
       Left _ ->
         error ("mrSetEVarClosed: incorrect instantiation for evar " ++
                showMRVar var ++
                "\nexpected type:\n" ++ showTerm var_tp ++
                "\nactual type:\n" ++ showTerm val_tp)
       Right _ -> return ()
     modify $ \st ->
       st { mrsVars =
            Map.alter
            (\case
                Just (EVarInfo Nothing) -> Just $ EVarInfo (Just val)
                Just (EVarInfo (Just _)) ->
                  error "Setting existential variable: variable already set!"
                _ -> error "Setting existential variable: not an evar!")
            var (mrsVars st) }


-- | Try to set the value of the application @X e1 .. en@ of evar @X@ to an
-- expression @e@ by trying to set @X@ to @\ x1 ... xn -> e@. This only works if
-- each free uvar @xi@ in @e@ is one of the arguments @ej@ to @X@ (though it
-- need not be the case that @i=j@). Return whether this succeeded.
mrTrySetAppliedEVar :: MRVar -> [Term] -> Term -> MRM Bool
mrTrySetAppliedEVar evar args t =
  -- Get the complete list of argument variables of the type of evar
  let (evar_vars, _) = asPiList (mrVarType evar) in
  -- Get all the free variables of t
  let free_vars = bitSetElems (looseVars t) in
  -- For each free var of t, find an arg equal to it
  case mapM (\i -> findIndex (\case
                                 (asLocalVar -> Just j) -> i == j
                                 _ -> False) args) free_vars of
    Just fv_arg_ixs
      -- Check to make sure we have the right number of args
      | length args == length evar_vars -> do
          -- Build a list of the input vars x1 ... xn as terms, noting that the
          -- first variable is the least recently bound and so has the highest
          -- deBruijn index
          let arg_ixs = reverse [0 .. length args - 1]
          arg_vars <- mapM (liftSC1 scLocalVar) arg_ixs

          -- For each free variable of t, we substitute the corresponding
          -- variable xi, substituting error terms for the variables that are
          -- not free (since we have nothing else to substitute for them)
          let var_map = zip free_vars fv_arg_ixs
          let subst_vars = if free_vars == [] then [] else
                             [0 .. maximum free_vars]
          let subst = flip map subst_vars $ \i ->
                maybe (error
                       ("mrTrySetAppliedEVar: unexpected free variable "
                        ++ show i ++ " in term\n" ++ showTerm t))
                (arg_vars !!) (lookup i var_map)
          body <- substTerm 0 subst t

          -- Now instantiate evar to \x1 ... xn -> body
          evar_inst <- liftSC2 scLambdaList evar_vars body
          mrSetEVarClosed evar evar_inst
          return True

    _ -> return False


-- | Replace all evars in a 'Term' with their instantiations when they have one
mrSubstEVars :: Term -> MRM Term
mrSubstEVars = memoFixTermFun $ \recurse t ->
  do var_map <- mrVars
     case t of
       -- If t is an instantiated evar, recurse on its instantiation
       (asEVarApp var_map -> Just (_, args, Just t')) ->
         mrApplyAll t' args >>= recurse
       -- If t is anything else, recurse on its immediate subterms
       _ -> traverseSubterms recurse t

-- | Replace all evars in a 'Term' with their instantiations, returning
-- 'Nothing' if we hit an uninstantiated evar
mrSubstEVarsStrict :: Term -> MRM (Maybe Term)
mrSubstEVarsStrict top_t =
  runMaybeT $ flip memoFixTermFun top_t $ \recurse t ->
  do var_map <- lift mrVars
     case t of
       -- If t is an instantiated evar, recurse on its instantiation
       (asEVarApp var_map -> Just (_, args, Just t')) ->
         lift (mrApplyAll t' args) >>= recurse
       -- If t is an uninstantiated evar, return Nothing
       (asEVarApp var_map -> Just (_, _, Nothing)) ->
         mzero
       -- If t is anything else, recurse on its immediate subterms
       _ -> traverseSubterms recurse t

-- | Makes 'mrSubstEVarsStrict' be marked as used
_mrSubstEVarsStrict :: Term -> MRM (Maybe Term)
_mrSubstEVarsStrict = mrSubstEVarsStrict

-- | Get the 'CoIndHyp' for a pair of 'FunName's, if there is one
mrGetCoIndHyp :: FunName -> FunName -> MRM (Maybe CoIndHyp)
mrGetCoIndHyp nm1 nm2 = Map.lookup (nm1, nm2) <$> mrCoIndHyps

-- | Run a compuation under an additional co-inductive assumption
withCoIndHyp :: CoIndHyp -> MRM a -> MRM a
withCoIndHyp hyp m =
  do debugPretty 2 ("withCoIndHyp" <+> ppInEmptyCtx hyp)
     hyps' <- Map.insert (coIndHypLHSFun hyp,
                          coIndHypRHSFun hyp) hyp <$> mrCoIndHyps
     local (\info -> info { mriCoIndHyps = hyps' }) m

-- | Generate fresh evars for the context of a 'CoIndHyp' and
-- substitute them into its arguments and right-hand side
instantiateCoIndHyp :: CoIndHyp -> MRM ([Term], [Term])
instantiateCoIndHyp (CoIndHyp {..}) =
  do evars <- mrFreshEVars coIndHypCtx
     lhs <- substTermLike 0 evars coIndHypLHS
     rhs <- substTermLike 0 evars coIndHypRHS
     return (lhs, rhs)

-- | Apply the invariants of a 'CoIndHyp' to their respective arguments,
-- yielding @Bool@ conditions, using the constant @True@ value when an
-- invariant is absent
applyCoIndHypInvariants :: CoIndHyp -> MRM (Term, Term)
applyCoIndHypInvariants hyp =
  let apply_invariant :: Maybe Term -> [Term] -> MRM Term
      apply_invariant (Just (asLambdaList -> (vars, phi))) args
        | length vars == length args
          -- NOTE: applying to a list of arguments == substituting the reverse
          -- of that list, because the first argument corresponds to the
          -- greatest deBruijn index
        = substTerm 0 (reverse args) phi
      apply_invariant (Just _) _ =
        error "applyCoIndHypInvariants: wrong number of arguments for invariant!"
      apply_invariant Nothing _ = liftSC1 scBool True in
  do invar1 <- apply_invariant (coIndHypInvariantLHS hyp) (coIndHypLHS hyp)
     invar2 <- apply_invariant (coIndHypInvariantRHS hyp) (coIndHypRHS hyp)
     return (invar1, invar2)

-- | Look up the 'FunAssump' for a 'FunName', if there is one
mrGetFunAssump :: FunName -> MRM (Maybe FunAssump)
mrGetFunAssump nm = Map.lookup nm <$> mrFunAssumps

-- | Run a computation under the additional assumption that a named function
-- applied to a list of arguments refines a given right-hand side, all of which
-- are 'Term's that can have the current uvars free
withFunAssump :: FunName -> [Term] -> NormComp -> MRM a -> MRM a
withFunAssump fname args rhs m =
  do k <- CompFunReturn <$> Type <$> mrFunOutType fname args
     mrDebugPPPrefixSep 1 "withFunAssump" (FunBind fname args k) "|=" rhs
     ctx <- mrUVars
     assumps <- mrFunAssumps
     let assump = FunAssump ctx args (RewriteFunAssump rhs)
     let assumps' = Map.insert fname assump assumps
     local (\info ->
             let env' = (mriEnv info) { mreFunAssumps = assumps' } in
             info { mriEnv = env' }) m

-- | Get the invariant hint associated with a function name, by unfolding the
-- name and checking if its body has the form
--
-- > \ x1 ... xn -> invariantHint a phi m
--
-- If so, return @\ x1 ... xn -> phi@ as a term with the @xi@ variables free.
-- Otherwise, return 'Nothing'. Note that this function will also look past
-- any initial @bindM ... (assertFiniteM ...)@ applications.
mrGetInvariant :: FunName -> MRM (Maybe Term)
mrGetInvariant nm =
  mrFunNameBody nm >>= \case
    Just body -> mrGetInvariantBody body
    _ -> return Nothing

-- | The main loop of 'mrGetInvariant', which operates on a function body
mrGetInvariantBody :: Term -> MRM (Maybe Term)
mrGetInvariantBody tm = case asApplyAll tm of
  -- go inside any top-level lambdas
  (asLambda -> Just (nm, tp, body), []) ->
    do body' <- liftSC1 betaNormalize body
       mb_phi <- mrGetInvariantBody body'
       liftSC3 scLambda nm tp `mapM` mb_phi
  -- always beta-reduce
  (f@(asLambda -> Just _), args) ->
    do tm' <- mrApplyAll f args
       mrGetInvariantBody tm'
  -- go inside any top-level applications of of bindM ... (assertFiniteM ...)
  (isGlobalDef "Prelude.bindM" -> Just (),
   [_, _,
    asApp -> Just (isGlobalDef "CryptolM.assertFiniteM" -> Just (),
                   asCtor -> Just (primName -> "Cryptol.TCNum", _)),
    k]) ->
    do pf <- liftSC1 scGlobalDef "Prelude.TrueI"
       body <- mrApplyAll k [pf]
       mrGetInvariantBody body
  -- otherwise, return Just iff there is a top-level invariant hint
  (isGlobalDef "Prelude.invariantHint" -> Just (),
   [_, phi, _]) -> return $ Just phi
  _ -> return Nothing

-- | Add an assumption of type @Bool@ to the current path condition while
-- executing a sub-computation
withAssumption :: Term -> MRM a -> MRM a
withAssumption phi m =
  do mrDebugPPPrefix 1 "withAssumption" phi
     assumps <- mrAssumptions
     assumps' <- liftSC2 scAnd phi assumps
     local (\info -> info { mriAssumptions = assumps' }) m

-- | Remove any existing assumptions and replace them with a Boolean term
withOnlyAssumption :: Term -> MRM a -> MRM a
withOnlyAssumption phi m =
  do mrDebugPPPrefix 1 "withOnlyAssumption" phi
     local (\info -> info { mriAssumptions = phi }) m

-- | Add a 'DataTypeAssump' to the current context while executing a
-- sub-computations
withDataTypeAssump :: Term -> DataTypeAssump -> MRM a -> MRM a
withDataTypeAssump x assump m =
  do mrDebugPPPrefixSep 1 "withDataTypeAssump" x "==" assump
     dataTypeAssumps' <- HashMap.insert x assump <$> mrDataTypeAssumps
     local (\info -> info { mriDataTypeAssumps = dataTypeAssumps' }) m

-- | Get the 'DataTypeAssump' associated to the given term, if one exists
mrGetDataTypeAssump :: Term -> MRM (Maybe DataTypeAssump)
mrGetDataTypeAssump x = HashMap.lookup x <$> mrDataTypeAssumps

-- | Convert a 'FunAssumpRHS' to a 'NormComp'
mrFunAssumpRHSAsNormComp :: FunAssumpRHS -> MRM NormComp
mrFunAssumpRHSAsNormComp (OpaqueFunAssump f args) =
  FunBind f args <$> CompFunReturn <$> Type <$> mrFunOutType f args
mrFunAssumpRHSAsNormComp (RewriteFunAssump rhs) = return rhs


----------------------------------------------------------------------
-- * Functions for Debug Output
----------------------------------------------------------------------

-- | Print a 'String' if the debug level is at least the supplied 'Int'
debugPrint :: Int -> String -> MRM ()
debugPrint i str =
  mrDebugLevel >>= \lvl ->
  if lvl >= i then liftIO (hPutStrLn stderr str) else return ()

-- | Print a document if the debug level is at least the supplied 'Int'
debugPretty :: Int -> SawDoc -> MRM ()
debugPretty i pp = debugPrint i $ renderSawDoc defaultPPOpts pp

-- | Pretty-print an object in the current context if the current debug level is
-- at least the supplied 'Int'
debugPrettyInCtx :: PrettyInCtx a => Int -> a -> MRM ()
debugPrettyInCtx i a = mrUVars >>= \ctx -> debugPrint i (showInCtx ctx a)

-- | Pretty-print an object relative to the current context
mrPPInCtx :: PrettyInCtx a => a -> MRM SawDoc
mrPPInCtx a = runPPInCtxM (prettyInCtx a) <$> mrUVars

-- | Pretty-print the result of 'ppWithPrefix' relative to the current uvar
-- context to 'stderr' if the debug level is at least the 'Int' provided
mrDebugPPPrefix :: PrettyInCtx a => Int -> String -> a -> MRM ()
mrDebugPPPrefix i pre a =
  mrUVars >>= \ctx ->
  debugPretty i $
  runPPInCtxM (group <$> nest 2 <$> ppWithPrefix pre a) ctx

-- | Pretty-print the result of 'ppWithPrefixSep' relative to the current uvar
-- context to 'stderr' if the debug level is at least the 'Int' provided
mrDebugPPPrefixSep :: (PrettyInCtx a, PrettyInCtx b) =>
                      Int -> String -> a -> String -> b -> MRM ()
mrDebugPPPrefixSep i pre a1 sp a2 =
  mrUVars >>= \ctx ->
  debugPretty i $
  runPPInCtxM (group <$> nest 2 <$> ppWithPrefixSep pre a1 sp a2) ctx
