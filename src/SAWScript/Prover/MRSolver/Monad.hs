{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

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

import Data.List (find, findIndex)
import qualified Data.Text as T
import System.IO (hPutStrLn, stderr)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans.Maybe

import Data.Map (Map)
import qualified Data.Map as Map

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
  | FailCtxMNF Term
  deriving Show

-- | That's MR. Failure to you
data MRFailure
  = TermsNotEq Term Term
  | TypesNotEq Type Type
  | CompsDoNotRefine NormComp NormComp
  | ReturnNotError Term
  | FunsNotEq FunName FunName
  | CannotLookupFunDef FunName
  | RecursiveUnfold FunName
  | MalformedLetRecTypes Term
  | MalformedDefsFun Term
  | MalformedComp Term
  | NotCompFunType Term
  | CoIndHypMismatchWidened FunName FunName CoIndHyp
  | CoIndHypMismatchFailure (NormComp, NormComp) (NormComp, NormComp)
    -- | A local variable binding
  | MRFailureLocalVar LocalName MRFailure
    -- | Information about the context of the failure
  | MRFailureCtx FailCtx MRFailure
    -- | Records a disjunctive branch we took, where both cases failed
  | MRFailureDisj MRFailure MRFailure
  deriving Show

-- | Pretty-print an object prefixed with a 'String' that describes it
ppWithPrefix :: PrettyInCtx a => String -> a -> PPInCtxM SawDoc
ppWithPrefix str a = (pretty str <>) <$> nest 2 <$> (line <>) <$> prettyInCtx a

-- | Pretty-print two objects, prefixed with a 'String' and with a separator
ppWithPrefixSep :: PrettyInCtx a => String -> a -> String -> a ->
                   PPInCtxM SawDoc
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
  prettyInCtx (FailCtxMNF t) =
    group <$> nest 2 <$> vsepM [return "When normalizing computation:",
                                prettyInCtx t]

instance PrettyInCtx MRFailure where
  prettyInCtx (TermsNotEq t1 t2) =
    ppWithPrefixSep "Could not prove terms equal:" t1 "and" t2
  prettyInCtx (TypesNotEq tp1 tp2) =
    ppWithPrefixSep "Types not equal:" tp1 "and" tp2
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
  prettyInCtx (CoIndHypMismatchWidened nm1 nm2 _) =
    ppWithPrefixSep "[Internal] Trying to widen co-inductive hypothesis on:" nm1 "," nm2
  prettyInCtx (CoIndHypMismatchFailure (tm1, tm2) (tm1', tm2')) =
    do pp <- ppWithPrefixSep "" tm1 "|=" tm2
       pp' <- ppWithPrefixSep "" tm1' "|=" tm2'
       return $ "Could not match co-inductive hypothesis:" <> pp' <> line <>
                                              "with goal:" <> pp
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
showMRFailure = showInCtx []


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
  -- | The uvars that were in scope when this assmption was created, in order
  -- from outermost to innermost; that is, the uvars as "seen from outside their
  -- scope", which is the reverse of the order of 'mrUVars', below
  coIndHypCtx :: [(LocalName,Term)],
  -- | The LHS argument expressions @y1, ..., ym@ over the 'coIndHypCtx' uvars
  coIndHypLHS :: [Term],
  -- | The RHS argument expressions @y1, ..., ym@ over the 'coIndHypCtx' uvars
  coIndHypRHS :: [Term]
} deriving Show

-- | A map from pairs of function names to co-inductive hypotheses over those
-- names
type CoIndHyps = Map (FunName, FunName) CoIndHyp

-- | An assumption that a named function refines some specificaiton. This has
-- the form
--
-- > forall x1, ..., xn. F e1 ... ek |= m
--
-- for some universal context @x1:T1, .., xn:Tn@, some list of argument
-- expressions @ei@ over the universal @xj@ variables, and some right-hand side
-- computation expression @m@.
data FunAssump = FunAssump {
  -- | The uvars that were in scope when this assmption was created, in order
  -- from outermost to innermost; that is, the uvars as "seen from outside their
  -- scope", which is the reverse of the order of 'mrUVars', below
  fassumpCtx :: [(LocalName,Term)],
  -- | The argument expressions @e1, ..., en@ over the 'fassumpCtx' uvars
  fassumpArgs :: [Term],
  -- | The right-hand side upper bound @m@ over the 'fassumpCtx' uvars
  fassumpRHS :: NormComp
}

-- | A map from function names to function refinement assumptions over that
-- name
type FunAssumps = Map FunName FunAssump

-- | Parameters and locals for MR. Solver
data MRInfo = MRInfo {
  -- | Global shared context for building terms, etc.
  mriSC :: SharedContext,
  -- | SMT timeout for SMT calls made by Mr. Solver
  mriSMTTimeout :: Maybe Integer,
  -- | The current context of universal variables, which are free SAW core
  -- variables, in order from innermost to outermost, i.e., where element @0@
  -- corresponds to deBruijn index @0@
  mriUVars :: [(LocalName,Type)],
  -- | The set of function refinements to be assumed by to Mr. Solver
  mriFunAssumps :: FunAssumps,
  -- | The current set of co-inductive hypotheses
  mriCoIndHyps :: CoIndHyps,
  -- | The current assumptions, which are conjoined into a single Boolean term;
  -- note that these have the current UVars free
  mriAssumptions :: Term,
  -- | The debug level, which controls debug printing
  mriDebugLevel :: Int
}

-- | State maintained by MR. Solver
data MRState = MRState {
  -- | The existential and letrec-bound variables
  mrsVars :: MRVarMap
}

-- | Mr. Monad, the monad used by MR. Solver, which has 'MRInfo' as as a
-- shared environment, 'MRState' as state, and 'MRFailure' as an exception
-- type, all over an 'IO' monad
newtype MRM a = MRM { unMRM :: ReaderT MRInfo (StateT MRState
                                              (ExceptT MRFailure IO)) a }
              deriving (Functor, Applicative, Monad, MonadIO,
                        MonadReader MRInfo, MonadState MRState,
                                            MonadError MRFailure)

instance MonadTerm MRM where
  mkTermF = liftSC1 scTermF
  liftTerm = liftSC3 incVars
  whnfTerm = liftSC1 scWhnf
  substTerm = liftSC3 instantiateVarList

-- | Get the current value of 'mriSC'
mrSC :: MRM SharedContext
mrSC = mriSC <$> ask

-- | Get the current value of 'mrSMTTimeout'
mrSMTTimeout :: MRM (Maybe Integer)
mrSMTTimeout = mriSMTTimeout <$> ask

-- | Get the current value of 'mrUVars'
mrUVars :: MRM [(LocalName,Type)]
mrUVars = mriUVars <$> ask

-- | Get the current value of 'mrFunAssumps'
mrFunAssumps :: MRM FunAssumps
mrFunAssumps = mriFunAssumps <$> ask

-- | Get the current value of 'mrCoIndHyps'
mrCoIndHyps :: MRM CoIndHyps
mrCoIndHyps = mriCoIndHyps <$> ask

-- | Get the current value of 'mrAssumptions'
mrAssumptions :: MRM Term
mrAssumptions = mriAssumptions <$> ask

-- | Get the current value of 'mrDebugLevel'
mrDebugLevel :: MRM Int
mrDebugLevel = mriDebugLevel <$> ask

-- | Get the current value of 'mrVars'
mrVars :: MRM MRVarMap
mrVars = mrsVars <$> get

-- | Run an 'MRM' computation and return a result or an error
runMRM :: SharedContext -> Maybe Integer -> Int -> FunAssumps ->
          MRM a -> IO (Either MRFailure a)
runMRM sc timeout debug assumps m =
  do true_tm <- scBool sc True
     let init_info = MRInfo { mriSC = sc, mriSMTTimeout = timeout,
                              mriDebugLevel = debug, mriFunAssumps = assumps,
                              mriUVars = [], mriCoIndHyps = Map.empty,
                              mriAssumptions = true_tm }
     let init_st = MRState { mrsVars = Map.empty }
     runExceptT $ flip evalStateT init_st $ flip runReaderT init_info $ unMRM m

-- | Apply a function to any failure thrown by an 'MRM' computation
mapFailure :: (MRFailure -> MRFailure) -> MRM a -> MRM a
mapFailure f m = catchError m (throwError . f)

-- | Try two different 'MRM' computations, combining their failures if needed.
-- Note that the 'MRState' will reset if the first computation fails.
mrOr :: MRM a -> MRM a -> MRM a
mrOr m1 m2 =
  catchError m1 $ \err1 ->
  catchError m2 $ \err2 ->
  throwError $ MRFailureDisj err1 err2

-- | Run an 'MRM' computation in an extended failure context
withFailureCtx :: FailCtx -> MRM a -> MRM a
withFailureCtx ctx = mapFailure (MRFailureCtx ctx)

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
-- * Monadic Operations on Terms
----------------------------------------------------------------------

-- | Apply a 'TermProj' to perform a projection on a 'Term'
doTermProj :: Term -> TermProj -> MRM Term
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
mrApplyAll f args = liftSC2 scApplyAll f args >>= liftSC1 betaNormalize

-- | Get the current context of uvars as a list of variable names and their
-- types as SAW core 'Term's, with the least recently bound uvar first, i.e., in
-- the order as seen "from the outside"
mrUVarCtx :: MRM [(LocalName,Term)]
mrUVarCtx = reverse <$> map (\(nm,Type tp) -> (nm,tp)) <$> mrUVars

-- | Get the type of a 'Term' in the current uvar context
mrTypeOf :: Term -> MRM Term
mrTypeOf t = mrUVarCtx >>= \ctx -> liftSC2 scTypeOf' (map snd ctx) t

-- | Check if two 'Term's are convertible in the 'MRM' monad
mrConvertible :: Term -> Term -> MRM Bool
mrConvertible = liftSC4 scConvertibleEval scTypeCheckWHNF True

-- | Take a 'FunName' @f@ for a monadic function of type @vars -> CompM a@ and
-- compute the type @CompM [args/vars]a@ of @f@ applied to @args@. Return the
-- type @[args/vars]a@ that @CompM@ is applied to.
mrFunOutType :: FunName -> [Term] -> MRM Term
mrFunOutType fname args =
  funNameType fname >>= \case
  (asPiList -> (vars, asCompM -> Just tp))
    | length vars == length args -> substTermLike 0 args tp
  ftype@(asPiList -> (vars, _)) ->
    do pp_ftype <- mrPPInCtx ftype
       pp_fname <- mrPPInCtx fname
       debugPrint 0 "mrFunOutType: function applied to the wrong number of args"
       debugPrint 0 ("Expected: " ++ show (length vars) ++
                     ", found: " ++ show (length args))
       debugPretty 0 ("For function: " <> pp_fname <> " with type: " <> pp_ftype)
       error"mrFunOutType"

-- | Turn a 'LocalName' into one not in a list, adding a suffix if necessary
uniquifyName :: LocalName -> [LocalName] -> LocalName
uniquifyName nm nms | notElem nm nms = nm
uniquifyName nm nms =
  case find (flip notElem nms) $
       map (T.append nm . T.pack . show) [(0::Int) ..] of
    Just nm' -> nm'
    Nothing -> error "uniquifyName"

-- | Run a MR Solver computation in a context extended with a universal
-- variable, which is passed as a 'Term' to the sub-computation. Note that any
-- assumptions made in the sub-computation will be lost when it completes.
withUVar :: LocalName -> Type -> (Term -> MRM a) -> MRM a
withUVar nm tp m =
  do nm' <- uniquifyName nm <$> map fst <$> mrUVars
     assumps' <- mrAssumptions >>= liftTerm 0 1
     local (\info -> info { mriUVars = (nm',tp) : mriUVars info,
                            mriAssumptions = assumps' }) $
       mapFailure (MRFailureLocalVar nm') (liftSC1 scLocalVar 0 >>= m)

-- | Run a MR Solver computation in a context extended with a universal variable
-- and pass it the lifting (in the sense of 'incVars') of an MR Solver term
withUVarLift :: TermLike tm => LocalName -> Type -> tm ->
                (Term -> tm -> MRM a) -> MRM a
withUVarLift nm tp t m =
  withUVar nm tp (\x -> liftTermLike 0 1 t >>= m x)

-- | Run a MR Solver computation in a context extended with a list of universal
-- variables, passing 'Term's for those variables to the supplied computation.
-- The variables are bound "outside in", meaning the first variable in the list
-- is bound outermost, and so will have the highest deBruijn index.
withUVars :: [(LocalName,Term)] -> ([Term] -> MRM a) -> MRM a
withUVars = helper [] where
  -- The extra input list gives the variables that have already been bound, in
  -- order from most to least recently bound
  helper :: [Term] -> [(LocalName,Term)] -> ([Term] -> MRM a) -> MRM a
  helper vars [] m = m $ reverse vars
  helper vars ((nm,tp):ctx) m =
    -- FIXME: I think substituting here is wrong, but works on closed terms, so
    -- it's fine to use at the top level at least...
    substTerm 0 vars tp >>= \tp' ->
    withUVarLift nm (Type tp') vars $ \var vars' -> helper (var:vars') ctx m

-- | Build 'Term's for all the uvars currently in scope, ordered from least to
-- most recently bound
getAllUVarTerms :: MRM [Term]
getAllUVarTerms =
  (length <$> mrUVars) >>= \len ->
  mapM (liftSC1 scLocalVar) [len-1, len-2 .. 0]

-- | Lambda-abstract all the current uvars out of a 'Term', with the least
-- recently bound variable being abstracted first
lambdaUVarsM :: Term -> MRM Term
lambdaUVarsM t = mrUVarCtx >>= \ctx -> liftSC2 scLambdaList ctx t

-- | Pi-abstract all the current uvars out of a 'Term', with the least recently
-- bound variable being abstracted first
piUVarsM :: Term -> MRM Term
piUVarsM t = mrUVarCtx >>= \ctx -> liftSC2 scPiList ctx t

-- | Instantiate all uvars in a term using the supplied function
instantiateUVarsM :: TermLike a => (LocalName -> Term -> MRM Term) -> a -> MRM a
instantiateUVarsM f a =
  do ctx <- mrUVarCtx
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

-- | Return a fresh sequence of existential variables for a context of variable
-- names and types, assuming each variable is free in the types that occur after
-- it in the list. Return the new evars all applied to the current uvars.
mrFreshEVars :: [(LocalName,Term)] -> MRM [Term]
mrFreshEVars = helper [] where
  -- Return fresh evars for the suffix of a context of variable names and types,
  -- where the supplied Terms are evars that have already been generated for the
  -- earlier part of the context, and so must be substituted into the remaining
  -- types in the context
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
     liftSC3 scCheckSubtype Nothing (TypedTerm val val_tp) var_tp
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
          let arg_ixs = [length args - 1, length args - 2 .. 0]
          arg_vars <- mapM (liftSC1 scLocalVar) arg_ixs

          -- For free variable of t, we substitute the corresponding variable
          -- xi, substituting error terms for the variables that are not free
          -- (since we have nothing else to substitute for them)
          let var_map = zip free_vars fv_arg_ixs
          let subst = flip map [0 .. length args - 1] $ \i ->
                maybe (error "mrTrySetAppliedEVar: unexpected free variable")
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

-- | Run a compuation under the additional co-inductive assumption that
-- @forall x1, ..., xn. F y1 ... ym |= G z1 ... zl@, where @F@ and @G@ are
-- the given 'FunName's, @y1, ..., ym@ and @z1, ..., zl@ are the given
-- argument lists, and @x1, ..., xn@ is the current context of uvars. If
-- while running the given computation a 'CoIndHypMismatchWidened' error is
-- reached with the given names, the state is restored and the computation is
-- re-run with the widened hypothesis. This is done recursively, meaning this
-- function will only return once no 'CoIndHypMismatchWidened' errors are
-- raised with the given names.
withCoIndHyp :: FunName -> [Term] -> FunName -> [Term] -> MRM a -> MRM a
withCoIndHyp nm1 args1 nm2 args2 m =
  do ctx <- mrUVarCtx
     withCoIndHyp' (nm1, nm2) (CoIndHyp ctx args1 args2) m

-- | The main loop of 'withCoIndHyp'
withCoIndHyp' :: (FunName, FunName) -> CoIndHyp -> MRM a -> MRM a
withCoIndHyp' (nm1, nm2) hyp@(CoIndHyp _ args1 args2) m =
  do mrDebugPPPrefixSep 1 "withCoIndHyp" (FunBind nm1 args1 CompFunReturn)
                                    "|=" (FunBind nm2 args2 CompFunReturn)
     st <- get
     hyps' <- Map.insert (nm1, nm2) hyp <$> mrCoIndHyps
     (local (\info -> info { mriCoIndHyps = hyps' }) m) `catchError` \case
       CoIndHypMismatchWidened nm1' nm2' hyp' | nm1 == nm1' && nm2 == nm2'
         -> -- FIXME: Could restoring the state here cause any problems?
            put st >> withCoIndHyp' (nm1, nm2) hyp' m
       e -> throwError e

-- | Generate fresh evars for the context of a 'CoIndHyp' and
-- substitute them into its arguments and right-hand side
instantiateCoIndHyp :: CoIndHyp -> MRM ([Term], [Term])
instantiateCoIndHyp (CoIndHyp {..}) =
  do evars <- mrFreshEVars coIndHypCtx
     lhs <- substTermLike 0 evars coIndHypLHS
     rhs <- substTermLike 0 evars coIndHypRHS
     return (lhs, rhs)

-- | Look up the 'FunAssump' for a 'FunName', if there is one
mrGetFunAssump :: FunName -> MRM (Maybe FunAssump)
mrGetFunAssump nm = Map.lookup nm <$> mrFunAssumps

-- | Run a computation under the additional assumption that a named function
-- applied to a list of arguments refines a given right-hand side, all of which
-- are 'Term's that can have the current uvars free
withFunAssump :: FunName -> [Term] -> NormComp -> MRM a -> MRM a
withFunAssump fname args rhs m =
  do mrDebugPPPrefixSep 1 "withFunAssump" (FunBind
                                           fname args CompFunReturn) "|=" rhs
     ctx <- mrUVarCtx
     assumps <- mrFunAssumps
     let assumps' = Map.insert fname (FunAssump ctx args rhs) assumps
     local (\info -> info { mriFunAssumps = assumps' }) m

-- | Generate fresh evars for the context of a 'FunAssump' and substitute them
-- into its arguments and right-hand side
instantiateFunAssump :: FunAssump -> MRM ([Term], NormComp)
instantiateFunAssump fassump =
  do evars <- mrFreshEVars $ fassumpCtx fassump
     args <- substTermLike 0 evars $ fassumpArgs fassump
     rhs <- substTermLike 0 evars $ fassumpRHS fassump
     return (args, rhs)

-- | Add an assumption of type @Bool@ to the current path condition while
-- executing a sub-computation
withAssumption :: Term -> MRM a -> MRM a
withAssumption phi m =
  do assumps <- mrAssumptions
     assumps' <- liftSC2 scAnd phi assumps
     local (\info -> info { mriAssumptions = assumps' }) m

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
debugPrettyInCtx i a =
  mrUVars >>= \ctx -> debugPrint i (showInCtx (map fst ctx) a)

-- | Pretty-print an object relative to the current context
mrPPInCtx :: PrettyInCtx a => a -> MRM SawDoc
mrPPInCtx a =
  runReader (prettyInCtx a) <$> map fst <$> mrUVars

-- | Pretty-print the result of 'ppWithPrefixSep' relative to the current uvar
-- context to 'stderr' if the debug level is at least the 'Int' provided
mrDebugPPPrefixSep :: PrettyInCtx a => Int -> String -> a -> String -> a ->
                      MRM ()
mrDebugPPPrefixSep i pre a1 sp a2 =
  mrUVars >>= \ctx ->
  debugPretty i $
  flip runReader (map fst ctx) (group <$> nest 2 <$>
                                ppWithPrefixSep pre a1 sp a2)