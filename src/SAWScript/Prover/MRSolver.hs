{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}

{- |
Module      : SAWScript.Prover.MRSolver
Copyright   : Galois, Inc. 2021
License     : BSD3
Maintainer  : westbrook@galois.com
Stability   : experimental
Portability : non-portable (language extensions)

This module implements a monadic-recursive solver, for proving that one monadic
term refines another. The algorithm works on the "monadic normal form" of
computations, which uses the following laws to simplify binds in computations,
where either is the sum elimination function defined in the SAW core prelude:

returnM x >>= k               = k x
errorM str >>= k              = errorM
(m >>= k1) >>= k2             = m >>= \x -> k1 x >>= k2
(existsM f) >>= k             = existsM (\x -> f x >>= k)
(forallM f) >>= k             = forallM (\x -> f x >>= k)
(orM m1 m2) >>= k             = orM (m1 >>= k) (m2 >>= k)
(if b then m1 else m2) >>= k  = if b then m1 >>= k else m2 >>1 k
(either f1 f2 e) >>= k        = either (\x -> f1 x >= k) (\x -> f2 x >= k) e
(letrecM funs body) >>= k     = letrecM funs (\F1 ... Fn -> body F1 ... Fn >>= k)

The resulting computations of one of the following forms:

returnM e  |  errorM str  |  existsM f  |  forallM f  |  orM m1 m2  |
if b then m1 else m2  |  either f1 f2 e  |  F e1 ... en  |  F e1 ... en >>= k  |
letrecM lrts B (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> m)

The form F e1 ... en refers to a recursively-defined function or a function
variable that has been locally bound by a letrecM. Either way, monadic
normalization does not attempt to normalize these functions.

The algorithm maintains a context of three sorts of variables: letrec-bound
variables, existential variables, and universal variables. Universal variables
are represented as free SAW core variables, while the other two forms of
variable are represented as SAW core 'ExtCns's terms, which are essentially
axioms that have been generated internally. These 'ExtCns's are Skolemized,
meaning that they take in as arguments all universal variables that were in
scope when they were created. The context also maintains a partial substitution
for the existential variables, as they become instantiated with values, and it
additionally remembers the bodies / unfoldings of the letrec-bound variables.

The goal of the solver at any point is of the form C |- m1 <= m2, meaning that
we are trying to prove m1 refines m2 in context C. This proceed by cases:

C |- returnM e1 <= returnM e2: prove C |- e1 = e2

C |- errorM str1 <= errorM str2: vacuously true

C |- if b then m1' else m1'' <= m2: prove C,b=true |- m1' <= m2 and
C,b=false |- m1'' <= m2, skipping either case where C,b=X is unsatisfiable;

C |- m1 <= if b then m2' else m2'': similar to the above

C |- either T U (CompM V) f1 f2 e <= m: prove C,x:T,e=inl x |- f1 x <= m and
C,y:U,e=inl y |- f2 y <= m, again skippping any case with unsatisfiable context;

C |- m <= either T U (CompM V) f1 f2 e: similar to previous

C |- m <= forallM f: make a new universal variable x and recurse

C |- existsM f <= m: make a new universal variable x and recurse (existential
elimination uses universal variables and vice-versa)

C |- m <= existsM f: make a new existential variable x and recurse

C |- forall f <= m: make a new existential variable x and recurse

C |- m <= orM m1 m2: try to prove C |- m <= m1, and if that fails, backtrack and
prove C |- m <= m2

C |- orM m1 m2 <= m: prove both C |- m1 <= m and C |- m2 <= m

C |- letrec (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> body) <= m: create
letrec-bound variables F1 through Fn in the context bound to their unfoldings f1
through fn, respectively, and recurse on body <= m

C |- m <= letrec (\F1 ... Fn -> (f1, ..., fn)) (\F1 ... Fn -> body): similar to
previous case

C |- F e1 ... en >>= k <= F e1' ... en' >>= k': prove C |- ei = ei' for each i
and then prove k x <= k' x for new universal variable x

C |- F e1 ... en <= F e1' ... en': prove C |- ei = ei' for each i

C |- F x1 ... xn <= m: if we have an assumption in the context C of the form
forall ys. F y1 ... yn <= m' then prove C |- [x1/y1, ..., xn/yn]m' <= m;
otherwise unfold F, replacing recursive calls to F with m, yielding some term
[m/F]F_body, and then prove C |- [m/F]F_body <= m; FIXME: eventually we should
do a "recursive unfolding" of F, which also unfolds any other function that is
mutually recursive with F but not with itself

C |- F e1 ... en >>= k <= m:

* If we have an assumption that F <= m', recursively prove C |- m' >>= k <= m
  (NOTE: assumptions are for functions we have already verified)

* If F is tail-recursive, make a new function F' with the same body as F except
  that each return e is replaced with a call to k e, and then proceed as in the
  C |- F' x1 ... xn <= m case, above (note that functions extracted from
  Heapster are generally tail recursive);

* Otherwise we don't know to "split" m into a bind of something that is refined
  by F e1 ... en and something the is refined by k, so just fail
-}

module SAWScript.Prover.MRSolver
  (askMRSolver, MRFailure(..), showMRFailure
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Data.Semigroup

import Data.Map (Map)
import qualified Data.Map as Map
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Prettyprinter

import Verifier.SAW.Term.Functor
import Verifier.SAW.Term.CtxTerm (MonadTerm(..))
import Verifier.SAW.Term.Pretty
import Verifier.SAW.SCTypeCheck
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer
import Verifier.SAW.Cryptol.Monadify

import SAWScript.Proof (boolToProp)
import qualified SAWScript.Prover.SBV as SBV


----------------------------------------------------------------------
-- * Utility Functions for Transforming 'Term's
----------------------------------------------------------------------

-- | Transform the immediate subterms of a term using the supplied function
traverseSubterms :: MonadTerm m => (Term -> m Term) -> Term -> m Term
traverseSubterms f (unwrapTermF -> tf) = traverse f tf >>= mkTermF

-- | Build a recursive memoized function for tranforming 'Term's. Take in a
-- function @f@ that intuitively performs one step of the transformation and
-- allow it to recursively call the memoized function being defined by passing
-- it as the first argument to @f@.
memoFixTermFun :: MonadIO m => ((Term -> m a) -> Term -> m a) -> Term -> m a
memoFixTermFun f term_top =
  do table_ref <- liftIO $ newIORef IntMap.empty
     let go t@(STApp { stAppIndex = ix }) =
           readIORef table_ref >>= \table ->
           case IntMap.lookup ix table of
             Just ret -> return ret
             Nothing ->
               do ret <- f go t
                  modifyIORef' table_ref (IntMap.insert ix ret)
                  return ret
         go t = f go t
     go term_top


----------------------------------------------------------------------
-- * MR Solver Term Representation
----------------------------------------------------------------------

-- | A variable used by the MR solver
newtype MRVar = MRVar { unMRVar :: ExtCns Term } deriving (Eq, Show, Ord)

-- | Test if a 'Term' is an application of an 'MRVar' to some arguments
asMRVarApp :: Recognizer Term (MRVar, [Term])
asMRVarApp (asApplyAll -> (asExtCns -> Just ec, args)) =
  return (MRVar ec, args)
asMRVarApp _ = Nothing

-- | Get the type of an 'MRVar'
mrVarType :: MRVar -> Term
mrVarType = ecType . unMRVar

-- | Names of functions to be used in computations, which are either local names
-- (represented with an 'ExtCns'), which have been created to represent
-- recursive calls to fixed-points, or global named constants
data FunName
  = LocalName (ExtCns Term) | GlobalName GlobalDef
  deriving (Eq, Show)

-- | Get the type of a 'FunName'
funNameType :: FunName -> Term
funNameType (LocalName ec) = ecType ec
funNameType (GlobalName gd) = globalDefType gd

-- | A term specifically known to be of type @sort i@ for some @i@
newtype Type = Type Term deriving Show

-- | A Haskell representation of a @CompM@ in "monadic normal form"
data WHNFComp
  = ReturnM Term -- ^ A term @returnM a x@
  | ErrorM Term -- ^ A term @errorM a str@
  | Ite Term Comp Comp -- ^ If-then-else computation
  | OrM Term Term -- ^ an @orM@ computation
  | ExistsM CompFun -- ^ an @existsM@ computation
  | ForallM CompFun -- ^ a @forallM@ computation
  | FunBind FunName [Term] CompFun
    -- ^ Bind a monadic function with @N@ arguments in an @a -> CompM b@ term
  deriving Show

-- | A computation function of type @a -> CompM b@ for some @a@ and @b@
data CompFun
     -- | An arbitrary term
  = CompFunTerm Term
    -- | A special case for the term @\ (x:a) -> returnM a x@
  | CompFunReturn
    -- | The monadic composition @f >=> g@
  | CompFunComp CompFun CompFun
  deriving Show

-- | A computation of type @CompM a@ for some @a@
data Comp = CompTerm Term | CompBind Comp CompFun
          deriving Show

-- | A universal type for all the different ways MR. Solver represents terms
data MRTerm
  = MRTermTerm Term
  | MRTermType Type
  | MRTermComp Comp
  | MRTermCompFun CompFun
  | MRTermWHNFComp WHNFComp
  | MRTermFunName FunName
  deriving Show

-- | Typeclass for things that can be coerced to 'MRTerm'
class IsMRTerm a where
  toMRTerm :: a -> MRTerm

instance IsMRTerm Term where toMRTerm = MRTermTerm
instance IsMRTerm Type where toMRTerm = MRTermType
instance IsMRTerm Comp where toMRTerm = MRTermComp
instance IsMRTerm CompFun where toMRTerm = MRTermCompFun
instance IsMRTerm WHNFComp where toMRTerm = MRTermWHNFComp
instance IsMRTerm FunName where toMRTerm = MRTermFunName


----------------------------------------------------------------------
-- * Pretty-Printing MR Solver Terms
----------------------------------------------------------------------

-- | The monad for pretty-printing in a context of SAW core variables
type PPInCtxM = Reader [LocalName]

-- | Pretty-print an object in a SAW core context and render to a 'String'
showInCtx :: PrettyInCtx a => [LocalName] -> a -> String
showInCtx ctx a =
  renderSawDoc defaultPPOpts $ runReader (prettyInCtx a) ctx

-- | A generic function for pretty-printing an object in a SAW core context of
-- locally-bound names
class PrettyInCtx a where
  prettyInCtx :: a -> PPInCtxM SawDoc

instance PrettyInCtx Term where
  prettyInCtx t = flip (ppTermInCtx defaultPPOpts) t <$> ask

-- | Combine a list of pretty-printed documents that represent an application
prettyAppList :: [PPInCtxM SawDoc] -> PPInCtxM SawDoc
prettyAppList = fmap (group . hang 2 . vsep) . sequence

instance PrettyInCtx Type where
  prettyInCtx (Type t) = prettyInCtx t

instance PrettyInCtx FunName where
  prettyInCtx (LocalName ec) = return $ ppName $ ecName ec
  prettyInCtx (GlobalName i) = return $ viaShow i

instance PrettyInCtx Comp where
  prettyInCtx (CompTerm t) = prettyInCtx t
  prettyInCtx (CompBind c f) =
    prettyAppList [prettyInCtx c, return ">>=", prettyInCtx f]

instance PrettyInCtx CompFun where
  prettyInCtx (CompFunTerm t) = prettyInCtx t
  prettyInCtx CompFunReturn = return "returnM"
  prettyInCtx (CompFunComp f g) =
    prettyAppList [prettyInCtx f, return ">=>", prettyInCtx g]

instance PrettyInCtx WHNFComp where
  prettyInCtx (ReturnM t) =
    prettyAppList [return "returnM", return "_", parens <$> prettyInCtx t]
  prettyInCtx (ErrorM str) =
    prettyAppList [return "errorM", return "_", parens <$> prettyInCtx str]
  prettyInCtx (Ite cond t1 t2) =
    prettyAppList [return "ite", return "_", prettyInCtx cond,
                   parens <$> prettyInCtx t1, parens <$> prettyInCtx t2]
  prettyInCtx (OrM t1 t2) =
    prettyAppList [return "orM", return "_",
                   parens <$> prettyInCtx t1, parens <$> prettyInCtx t2]
  prettyInCtx (ExistsM f) =
    prettyAppList [return "existsM", return "_", return "_",
                   parens <$> prettyInCtx f]
  prettyInCtx (ForallM f) =
    prettyAppList [return "forallM", return "_", return "_",
                   parens <$> prettyInCtx f]
  prettyInCtx (FunBind f [] k) =
    prettyAppList [prettyInCtx f, return ">>=", prettyInCtx k]
  prettyInCtx (FunBind f args k) =
    prettyAppList
    [parens <$> prettyAppList (prettyInCtx f : map prettyInCtx args),
     return ">>=", prettyInCtx k]

instance PrettyInCtx MRTerm where
  prettyInCtx (MRTermTerm t) = prettyInCtx t
  prettyInCtx (MRTermType tp) = prettyInCtx tp
  prettyInCtx (MRTermComp comp) = prettyInCtx comp
  prettyInCtx (MRTermCompFun f) = prettyInCtx f
  prettyInCtx (MRTermWHNFComp norm) = prettyInCtx norm
  prettyInCtx (MRTermFunName nm) = prettyInCtx nm


----------------------------------------------------------------------
-- * Lifting MR Solver Terms
----------------------------------------------------------------------

-- | Generic function for lifting a MR solver term
class MRLiftTerm a where
  mrLiftTerm :: MonadTerm m => DeBruijnIndex -> DeBruijnIndex -> a -> m a

instance MRLiftTerm Term where
  mrLiftTerm = liftTerm

instance MRLiftTerm Type where
  mrLiftTerm n i (Type tp) = Type <$> liftTerm n i tp

instance MRLiftTerm WHNFComp where
  mrLiftTerm n i (ReturnM t) = ReturnM <$> mrLiftTerm n i t
  mrLiftTerm n i (ErrorM str) = ErrorM <$> mrLiftTerm n i str
  mrLiftTerm n i (Ite cond t1 t2) =
    Ite <$> mrLiftTerm n i cond <*> mrLiftTerm n i t1 <*> mrLiftTerm n i t2
  mrLiftTerm n i (OrM t1 t2) = OrM <$> mrLiftTerm n i t1 <*> mrLiftTerm n i t2
  mrLiftTerm n i (ExistsM f) = ExistsM <$> mrLiftTerm n i f
  mrLiftTerm n i (ForallM f) = ForallM <$> mrLiftTerm n i f
  mrLiftTerm n i (FunBind nm args f) =
    FunBind nm <$> mapM (mrLiftTerm n i) args <*> mrLiftTerm n i f

instance MRLiftTerm CompFun where
  mrLiftTerm n i (CompFunTerm t) = CompFunTerm <$> mrLiftTerm n i t
  mrLiftTerm n i CompFunReturn = return CompFunReturn
  mrLiftTerm n i (CompFunComp f g) =
    CompFunComp <$> mrLiftTerm n i f <*> mrLiftTerm n i g

instance MRLiftTerm Comp where
  mrLiftTerm n i (CompTerm t) = CompTerm <$> mrLiftTerm n i t
  mrLiftTerm n i (CompBind m f) = CompBind <$> mrLiftTerm n i m <*> mrLiftTerm n i f

instance MRLiftTerm MRTerm where
  mrLiftTerm n i (MRTermTerm t) = MRTermTerm <$> mrLiftTerm n i t
  mrLiftTerm n i (MRTermType tp) = MRTermType <$> mrLiftTerm n i tp
  mrLiftTerm n i (MRTermComp m) = MRTermComp <$> mrLiftTerm n i m
  mrLiftTerm n i (MRTermCompFun f) = MRTermCompFun <$> mrLiftTerm n i f
  mrLiftTerm n i (MRTermWHNFComp m) = MRTermWHNFComp <$> mrLiftTerm n i m
  mrLiftTerm n i (MRTermFunName nm) = return $ MRTermFunName nm


----------------------------------------------------------------------
-- * MR Solver Errors
----------------------------------------------------------------------

-- | The context in which a failure occurred
data FailCtx
  = FailCtxCmp MRTerm MRTerm
  | FailCtxWHNF Term
  deriving Show

-- | That's MR. Failure to you
data MRFailure
  = TermsNotEq Term Term
  | TypesNotEq Type Type
  | ReturnNotError Term
  | FunsNotEq FunName FunName
  | CannotLookupFunDef FunName
  | RecursiveUnfold FunName
  | MalformedLetRecTypes Term
  | MalformedDefsFun Term
  | MalformedComp Term
  | NotCompFunType Term
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
  prettyInCtx (FailCtxCmp t1 t2) =
    group <$> nest 2 <$> vsepM [return "When comparing terms:",
                                prettyInCtx t1, prettyInCtx t2]
  prettyInCtx (FailCtxWHNF t) =
    group <$> nest 2 <$> vsepM [return "When normalizing computation:",
                                prettyInCtx t]

instance PrettyInCtx MRFailure where
  prettyInCtx (TermsNotEq t1 t2) =
    ppWithPrefixSep "Could not prove terms equal:" t1 "and" t2
  prettyInCtx (TypesNotEq tp1 tp2) =
    ppWithPrefixSep "Types not equal:" tp1 "and" tp2
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

-- | Recognize an evar applied to 0 or more arguments relative to a 'MRVarMap'
-- along with its instantiation, if any
asEVarApp :: MRVarMap -> Recognizer Term (MRVar, [Term], Maybe Term)
asEVarApp var_map (asMRVarApp -> Just (var, args))
  | Just (EVarInfo maybe_inst) <- Map.lookup var var_map =
    Just (var, args, maybe_inst)
asEVarApp _ _ = Nothing

-- | State maintained by MR. Solver
data MRState = MRState {
  -- | Global shared context for building terms, etc.
  mrSC :: SharedContext,
  -- | Global SMT configuration for the duration of the MR. Solver call
  mrSMTConfig :: SBV.SMTConfig,
  -- | SMT timeout for SMT calls made by Mr. Solver
  mrSMTTimeout :: Maybe Integer,
  -- | The context of universal variables, which are free SAW core variables
  mrUVars :: [(LocalName,Term)],
  -- | The existential and letrec-bound variables
  mrVars :: MRVarMap,
  -- | The current assumptions of function refinement, where we assume each
  -- left-hand in the list side refines its corresponding right-hand side
  mrFunRefs :: [(FunName, Term)],
  -- | The current assumptions, which are conjoined into a single Boolean term
  mrAssumptions :: Term
}

-- | Mr. Monad, the monad used by MR. Solver, which is the state-exception monad
type MRM = StateT MRState (ExceptT MRFailure IO)

instance MonadTerm MRM where
  mkTermF = liftSC1 scTermF
  liftTerm = liftSC3 incVars
  whnfTerm = liftSC1 scWhnf
  substTerm = liftSC3 instantiateVarList

-- | Run an 'MRM' computation, and apply a function to any failure thrown
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

-- | Catch any errors thrown by a computation and coerce them to a 'Left'
catchErrorEither :: MonadError e m => m a -> m (Either e a)
catchErrorEither m = catchError (Right <$> m) (return . Left)

-- FIXME: replace these individual lifting functions with a more general
-- typeclass like LiftTCM

-- | Lift a nullary SharedTerm computation into 'MRM'
liftSC0 :: (SharedContext -> IO a) -> MRM a
liftSC0 f = (mrSC <$> get) >>= \sc -> liftIO (f sc)

-- | Lift a unary SharedTerm computation into 'MRM'
liftSC1 :: (SharedContext -> a -> IO b) -> a -> MRM b
liftSC1 f a = (mrSC <$> get) >>= \sc -> liftIO (f sc a)

-- | Lift a binary SharedTerm computation into 'MRM'
liftSC2 :: (SharedContext -> a -> b -> IO c) -> a -> b -> MRM c
liftSC2 f a b = (mrSC <$> get) >>= \sc -> liftIO (f sc a b)

-- | Lift a ternary SharedTerm computation into 'MRM'
liftSC3 :: (SharedContext -> a -> b -> c -> IO d) -> a -> b -> c -> MRM d
liftSC3 f a b c = (mrSC <$> get) >>= \sc -> liftIO (f sc a b c)

-- | Lift a quaternary SharedTerm computation into 'MRM'
liftSC4 :: (SharedContext -> a -> b -> c -> d -> IO e) -> a -> b -> c -> d ->
           MRM e
liftSC4 f a b c d = (mrSC <$> get) >>= \sc -> liftIO (f sc a b c d)

-- | Run a MR Solver computation in a context extended with a universal
-- variable, which is passed as a 'Term' to the sub-computation
withUVar :: LocalName -> Type -> (Term -> MRM a) -> MRM a
withUVar nm (Type tp) m =
  mapFailure (MRFailureLocalVar nm) $
  do st <- get
     put (st { mrUVars = (nm,tp) : mrUVars st })
     ret <- liftSC1 scLocalVar 0 >>= m
     modify (\st' -> st' { mrUVars = mrUVars st })
     return ret

-- | Run a MR Solver computation in a context extended with a universal variable
-- and pass it the lifting (in the sense of 'incVars') of an MR Solver term
withUVarLift :: MRLiftTerm tm => LocalName -> Type -> tm ->
                (Term -> tm -> MRM a) -> MRM a
withUVarLift nm tp t m =
  withUVar nm tp (\x -> mrLiftTerm 0 1 t >>= m x)

-- | Build 'Term's for all the uvars currently in scope, ordered from least to
-- most recently bound
getAllUVarTerms :: MRM [Term]
getAllUVarTerms =
  (length <$> mrUVars <$> get) >>= \len ->
  mapM (liftSC1 scLocalVar) [len-1, len-2 .. 0]

-- | Lambda-abstract all the current uvars out of a 'Term', with the least
-- recently bound variable being abstracted first
lambdaUVarsM :: Term -> MRM Term
lambdaUVarsM t =
  (mrUVars <$> get) >>= \ctx ->
  liftSC2 scLambdaList (reverse ctx) t

-- | Pi-abstract all the current uvars out of a 'Term', with the least recently
-- bound variable being abstracted first
piUVarsM :: Term -> MRM Term
piUVarsM t =
  (mrUVars <$> get) >>= \ctx ->
  liftSC2 scPiList (reverse ctx) t

-- | Convert an 'MRVar' to a 'Term'
mrVarTerm :: MRVar -> MRM Term
mrVarTerm (MRVar ec) = liftSC1 scExtCns ec

-- | Get the 'VarInfo' associated with a 'MRVar'
mrVarInfo :: MRVar -> MRM (Maybe MRVarInfo)
mrVarInfo var = Map.lookup var <$> mrVars <$> get

-- | Get the current value of an evar, if it has one
mrGetEVar :: MRVar -> MRM (Maybe Term)
mrGetEVar var =
  mrVarInfo var >>= \case
  Just (EVarInfo maybe_tm) -> return maybe_tm
  Just _ -> error "mrGetEVar: Non-evar"
  Nothing -> error "mrGetEVar: Unknown var"

-- | Make a fresh 'MRVar' of a given type with the given info
mrFreshVar :: LocalName -> Type -> MRVarInfo -> MRM MRVar
mrFreshVar nm (Type tp) info =
  do ec <- liftSC2 scFreshEC nm tp
     let var = MRVar ec
     evar_tm <- liftSC1 scExtCns ec
     modify $ \st -> st { mrVars = Map.insert var info (mrVars st) }
     return var

-- | Make a fresh existential variable of the given type, abstracting out all
-- the current uvars and returning the new evar applied to all current uvars
mrFreshEVar :: LocalName -> Type -> MRM Term
mrFreshEVar nm (Type tp) =
  do tp' <- piUVarsM tp
     var <- mrFreshVar nm (Type tp') (EVarInfo Nothing)
     var_tm <- mrVarTerm var
     vars <- getAllUVarTerms
     liftSC2 scApplyAll var_tm vars

-- | Make a fresh function variable of the given type with the given body
mrFreshFunVar :: LocalName -> Type -> Term -> MRM MRVar
mrFreshFunVar nm tp body = mrFreshVar nm tp (FunVarInfo body)

-- | Set the value of an evar to a closed term
mrSetEVarClosed :: MRVar -> Term -> MRM ()
mrSetEVarClosed var val =
  do val_tp <- liftSC1 scTypeOf val
     -- FIXME: catch subtyping errors and report them as being evar failures
     liftSC3 scCheckSubtype Nothing (TypedTerm val val_tp) (mrVarType var)
     modify $ \st ->
       st { mrVars =
            Map.alter
            (\case
                Just (EVarInfo Nothing) -> Just $ EVarInfo (Just val)
                Just (EVarInfo (Just _)) ->
                  error "Setting existential variable: variable already set!"
                _ -> error "Setting existential variable: not an evar!")
            var (mrVars st) }


-- | Try to set the value of the application @X e1 .. en@ of evar @X@ to an
-- expression @e@ by trying to set @X@ to @\ x1 ... xn -> e@. This only works if
-- each free uvar @xi@ in @e@ is one of the arguments @ej@ to @X@ (though it
-- need not be the case that @i=j@). Return whether this succeeded.
mrTrySetAppliedEVar :: MRVar -> [Term] -> Term -> MRM Bool
mrTrySetAppliedEVar evar args t =
  -- Get the complete list of argument variables of the type of evar
  let (evar_vars, _) = asPiList (mrVarType var) in
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
          let arg_ixs = [length args - 1, length args - 2, .., 0]
          arg_vars <- mapM (liftSC1 scLocalVar) arg_ixs

          -- For free variable of t, we substitute the corresponding variable
          -- xi, substituting error terms for the variables that are not free
          -- (since we have nothing else to substitute for them)
          let var_map = zip free_vars fv_arg_ixs
          let subst = flip map [0, .., length args - 1] \i ->
                maybe (error "mrTrySetAppliedEVar: unexpected free variable")
                (arg_vars !!) (lookup i var_map)
          body <- substTerm 0 subst t

          -- Now build \x1 ... xn -> body as a term and set evar to that term
          var_inst <- liftSC2 scLambdaList var_vars body
          mrSetEVarClosed var var_inst
          return True

    _ -> False


-- | Replace all evars in a 'Term' with their instantiations when they have one
mrSubstEVars :: Term -> MRM Term
mrSubstEVars = memoFixTermFun $ \recurse t ->
  do var_map <- mrVars <$> get
     case t of
       -- If t is an instantiated evar, recurse on its instantiation
       (asEVarApp var_map -> Just (_, args, Just t')) ->
         liftSC2 scApplyAll t' args >>= recurse
       -- If t is anything else, recurse on its immediate subterms
       _ -> traverseSubterms recurse t

-- | Replace all evars in a 'Term' with their instantiations, returning
-- 'Nothing' if we hit an uninstantiated evar
mrSubstEVarsStrict :: Term -> MRM (Maybe Term)
mrSubstEVarsStrict = runMaybeT $ memoFixTermFun $ \recurse t ->
  do var_map <- mrVars <$> get
     case t of
       -- If t is an instantiated evar, recurse on its instantiation
       (asEVarApp var_map -> Just (_, args, Just t')) ->
         lift (liftSC2 scApplyAll t' args) >>= recurse
       -- If t is an uninstantiated evar, return Nothing
       (asEVarApp var_map -> Just (_, args, Nothing)) ->
         mzero
       -- If t is anything else, recurse on its immediate subterms
       _ -> traverseSubterms recurse t


----------------------------------------------------------------------
-- * Calling Out to SMT
----------------------------------------------------------------------

-- | Test if a closed Boolean term is "provable", i.e., its negation is
-- unsatisfiable, using an SMT solver. By "closed" we mean that it contains no
-- uvars or 'MRVar's.
mrProvableRaw :: Term -> MRM Bool
mrProvableRaw bool_prop =
  do smt_conf <- mrSMTConfig <$> get
     timeout <- mrSMTTimeout <$> get
     prop <- liftSC2 boolToProp [] bool_prop
     (smt_res, _) <- liftSC4 SBV.proveUnintSBVIO smt_conf mempty timeout prop
     case smt_res of
       Just _ -> return False
       Nothing -> return True

-- | Test if a Boolean term over the current uvars is provable given the current
-- assumptions
mrProvable :: Term -> MRM Bool
mrProvable bool_tm =
  do assumps <- mrAssumptions <$> get
     prop <- liftSC2 scImplies assumps bool_tm >>= liftSC1 scEqTrue
     forall_prop <- piUVarsM prop
     mrProvableRaw forall_prop


-- | A "simple" strategy for proving equality between two terms, which we assume
-- are of the same type. This strategy first checks if either side is an
-- uninstantiated evar, in which case it set that evar to the other side. If
-- not, it builds an equality proposition by applying the supplied function to
-- both sides, and passes this proposition to an SMT solver.
mrProveEqSimple :: (Term -> Term -> MRM Term) -> MRVarMap -> Term -> Term ->
                   MRM ()

-- If t1 is an instantiated evar, substitute and recurse
mrProveEqSimple eqf var_map (asEVarApp var_map -> Just (_, args, Just f)) t2 =
  liftSC2 scApplyAll f args >>= \t1' -> mrProveEqSimple eqf var_map t1' t2

-- If t1 is an uninstantiated evar, instantiate it with t2
mrProveEqSimple _ var_map t1@(asEVarApp var_map ->
                              Just (evar, args, Nothing)) t2 =
  do t2' <- mrSubstEVars t2
     success <- mrTrySetAppliedEVar evar args t2'
     if success then return () else throwError (TermsNotEq t1 t2)

-- If t2 is an instantiated evar, substitute and recurse
mrProveEqSimple eqf var_map t1 (asEVarApp -> Just (_, args, f)) =
  liftSC2 scApplyAll f args >>= \t2' -> mrProveEqSimple eqf var_map t1 t2'

-- If t2 is an uninstantiated evar, instantiate it with t1
mrProveEqSimple _ var_map t1 t2@(asEVarApp var_map ->
                                 Just (evar, args, Nothing)) =
  do t1' <- mrSubstEVars t1
     success <- mrTrySetAppliedEVar evar args t1
     if success then return () else throwError (TermsNotEq t1 t2)

-- Otherwise, try to prove both sides are equal. The use of mrSubstEVars instead
-- of mrSubstEVarsStrict means that we allow evars in the terms we send to the
-- SMT solver, but we treat them as uvars.
mrProveEqSimple eqf _ t1 t2 =
  do t1' <- mrSubstEVars t1
     t2' <- mrSubstEVars t2
     prop <- eqf t1' t2'
     succ <- mrProvable prop
     if succ then return () else
       throwError (TermsNotEq t1 t2)


-- | Prove that two terms are equal, instantiating evars if necessary, or
-- throwing an error if this is not possible
mrProveEq :: Term -> Term -> MRM ()
mrProveEq t1_top t2_top =
  (do tp <- liftSC1 scTypeOf t1_top
      varmap <- mrVars <$> get
      proveEq varmap tp t1_top t2_top)
  where
    proveEq :: Map MRVar MRVarInfo -> Term -> Term -> Term -> MRM ()
    proveEq var_map (asDataType -> (pn, [])) t1 t2
      | pn == "Prelude.Nat" =
        mrProveEqSimple (liftSC2 scEqualNat) var_map t1 t2
    proveEq var_map (asBitvectorType -> Just _) t1 t2 =
      -- FIXME: make a better solver for bitvector equalities
      mrProveEqSimple (liftSC2 scEq) var_map t1 t2
    proveEq var_map _ t1 t2 =
      mrProveEqSimple (liftSC2 scEq) var_map t1 t2


----------------------------------------------------------------------
-- * Normalizing and Matching on Terms
----------------------------------------------------------------------

FIXME HERE NOW: update the rest of MR solver!

-- | Get the input type of a computation function
compFunInputType :: CompFun -> MRM Term
compFunInputType (CompFunTerm t) =
  do tp <- liftSC1 scTypeOf t
     case asPi tp of
       Just (_, tp_in, _) -> return tp_in
       Nothing -> error "compFunInputType: Pi type expected!"
compFunInputType (CompFunComp f _) = compFunInputType f
compFunInputType (CompFunMark f _) = compFunInputType f

-- | Match a term as a function name
asFunName :: Term -> Maybe FunName
asFunName t =
  (LocalName <$> MRVar <$> asExtCns t)
  `mplus` (GlobalName <$> asTypedGlobalDef t)

-- | Match a term as being of the form @CompM a@ for some @a@
asCompMApp :: Term -> Maybe Term
asCompMApp (asApp -> Just (isGlobalDef "Prelude.CompM" -> Just (), tp)) =
  return tp
asCompMApp _ = fail "not CompM app"

-- | Apply a computation function to a term argument to get a computation
applyCompFun :: CompFun -> Term -> MRM Comp
applyCompFun (CompFunComp f g) t =
  -- (f >=> g) t == f t >>= g
  do comp <- applyCompFun f t
     return $ CompBind comp g
applyCompFun (CompFunTerm f) t =
  CompTerm <$> liftSC2 scApply f t
applyCompFun (CompFunMark f mark) t =
  do comp <- applyCompFun f t
     return $ CompMark comp mark


-- | Take in a @LetRecTypes@ list (as a SAW core term) and build a fresh
-- function variable for each @LetRecType@ in it
mkFunVarsForTps :: Term -> MRM [MRVar]
mkFunVarsForTps (asCtor -> Just (primName -> "Prelude.LRT_Nil", [])) =
  return []
mkFunVarsForTps (asCtor -> Just (primName -> "Prelude.LRT_Cons", [lrt, lrts])) =
  do tp <- liftSC1 completeOpenTerm $
       applyOpenTerm (globalOpenTerm "Prelude.lrtToType") (closedOpenTerm lrt)
     f <- MRVar <$> liftSC2 scFreshEC "f" tp
     (f:) <$> mkFunVarsForTps lrts
mkFunVarsForTps t = throwError (MalformedLetRecTypes t)

-- | Normalize a computation to weak head normal form
whnfComp :: Comp -> MRM WHNFComp
whnfComp (CompBind m f) =
  do norm <- whnfComp m
     whnfBind norm f
whnfComp (CompMark m mark) =
  do norm <- whnfComp m
     whnfMark norm mark
whnfComp (CompTerm t) =
  withFailureCtx (FailCtxWHNF t) $
  do t' <- liftSC1 scWhnf t
     case asApplyAll t' of
       (isGlobalDef "Prelude.returnM" -> Just (), [_, x]) ->
         return $ Return x
       (isGlobalDef "Prelude.bindM" -> Just (), [_, _, m, f]) ->
         do norm <- whnfComp (CompTerm m)
            whnfBind norm (CompFunTerm f)
       (isGlobalDef "Prelude.errorM" -> Just (), [_]) ->
         return Error
       (isGlobalDef "Prelude.ite" -> Just (), [_, cond, then_tm, else_tm]) ->
         return $ If cond (CompTerm then_tm) (CompTerm else_tm)
       (isGlobalDef "Prelude.letRecM" -> Just (), [tps, _, defs_f, body_f]) ->
         do
           -- First, make fresh function constants for all the bound functions
           funs <- mkFunVarsForTps tps
           fun_tms <- mapM mrVarTerm funs

           -- Next, tuple the constants up and apply the definition function
           -- defs_f to that tuple, yielding the definitions of the individual
           -- letrec-bound functions in terms of the new function constants
           funs_tm <-
              foldr ((=<<) . liftSC2 scPairValue) (liftSC0 scUnitValue) fun_tms
           defs_tm <- liftSC2 scApply defs_f funs_tm >>= liftSC1 scWhnf
           defs <- case asTupleValue defs_tm of
             Just defs -> return defs
             Nothing -> throwError (MalformedDefsFun defs_f)

           -- Remember the body associated with each fresh function constant
           modify $ \st -> st { mrVars = zip funs defs : mrVars st }

           -- Finally, apply the body function to the tuple of constants and
           -- recursively normalize the resulting computation
           body_tm <- liftSC2 scApply body_f funs_tm
           whnfComp (CompTerm body_tm)

       ((asFunName -> Just f), args) ->
         do comp_tp <- liftSC1 scTypeOf t >>= liftSC1 scWhnf
            tp <-
              case asCompMApp comp_tp of
                Just tp -> return tp
                _ -> error "Computation not of type CompM a for some a"
            ret_fun <- liftSC1 scGlobalDef "Prelude.returnM"
            g <- liftSC2 scApply ret_fun tp
            return $ FunBind f args mempty (CompFunTerm g)
       _ -> throwError (MalformedComp t')


-- | Bind a computation in whnf with a function, and normalize
whnfBind :: WHNFComp -> CompFun -> MRM WHNFComp
whnfBind (Return t) f = applyCompFun f t >>= whnfComp
whnfBind Error _ = return Error
whnfBind (If cond comp1 comp2) f =
  return $ If cond (CompBind comp1 f) (CompBind comp2 f)
whnfBind (FunBind f args mark g) h =
  return $ FunBind f args mark (CompFunComp g h)

-- | Mark a normalized computation
whnfMark :: WHNFComp -> Mark -> MRM WHNFComp
whnfMark (Return t) _ = return $ Return t
whnfMark Error _ = return Error
whnfMark (If cond comp1 comp2) mark =
  return $ If cond (CompMark comp1 mark) (CompMark comp2 mark)
whnfMark (FunBind f args mark1 g) mark2 =
  return $ FunBind f args (mark1 `mappend` mark2) (CompFunMark g mark2)

-- | Lookup the definition of a function or throw a 'CannotLookupFunDef' if this is
-- not allowed, either because it is a global function we are treating as opaque
-- or because it is a locally-bound function variable
mrLookupFunDef :: FunName -> MRM Term
mrLookupFunDef f@(GlobalName _) = throwError (CannotLookupFunDef f)
mrLookupFunDef f@(LocalName var) =
  mrVarInfo var >>= \case
  Just (FunVarInfo body) -> return body
  Just _ -> throwError (CannotLookupFunDef f)
  Nothing -> error "mrLookupFunDef: unknown variable!"

-- | Unfold a call to function @f@ in term @f args >>= g@
mrUnfoldFunBind :: FunName -> [Term] -> Mark -> CompFun -> MRM Comp
mrUnfoldFunBind f _ mark _ | inMark f mark = throwError (RecursiveUnfold f)
mrUnfoldFunBind f args mark g =
  do f_def <- mrLookupFunDef f
     CompBind <$>
       (CompMark <$> (CompTerm <$> liftSC2 scApplyAll f_def args)
        <*> (return $ singleMark f `mappend` mark))
       <*> return g


----------------------------------------------------------------------
-- * MR Solver Itself
----------------------------------------------------------------------

FIXME HERE NOW: update the rest of MR Solver

-- | Coinductively prove an equality between two named functions by assuming
-- the names are equal and proving their bodies equal
mrSolveCoInd :: FunName -> FunName -> MRM ()
mrSolveCoInd f1 f2 =
  do def1 <- mrLookupFunDef f1
     def2 <- mrLookupFunDef f2
     saved <- get
     put $ saved { mrFunEqs = ((f1,f2),True) : mrFunEqs saved }
     catchError (mrSolveEq (CompFunMark (CompFunTerm def1) (singleMark f1))
                 (CompFunMark (CompFunTerm def2) (singleMark f2))) $ \err ->
       -- NOTE: any equalities proved under the assumption that f1 == f2 are
       -- suspect, so we have to throw them out and revert to saved on error
       (put saved >> throwError err)


-- | Typeclass for proving that two (representations of) objects of the same SAW
-- core type @a@ are equivalent, where the notion of equivalent depends on the
-- type @a@. This assumes that the two objects have the same SAW core type. The
-- 'MRM' computation returns @()@ on success and throws a 'MRFailure' on error.
class (IsMRTerm a, IsMRTerm b) => MRSolveEq a b where
  mrSolveEq' :: a -> b -> MRM ()

-- | The main function for solving equations, that calls @mrSovleEq'@ but with
-- debugging support for errors, i.e., adding to the failure context
mrSolveEq :: MRSolveEq a b => a -> b -> MRM ()
mrSolveEq a b =
  withFailureCtx (FailCtxCmp (toMRTerm a) (toMRTerm b)) $ mrSolveEq' a b

-- NOTE: this instance is specifically for terms of non-computation type
instance MRSolveEq Term Term where
  mrSolveEq' t1 t2 =
    do eq <- mrTermsEq t1 t2
       if eq then return () else throwError (TermsNotEq t1 t2)

instance MRSolveEq Type Type where
  mrSolveEq' tp1@(Type t1) tp2@(Type t2) =
    do eq <- liftSC3 scConvertible True t1 t2
       if eq then return () else
         throwError (TypesNotEq tp1 tp2)

instance MRSolveEq FunName FunName where
  mrSolveEq' f1 f2 | f1 == f2 = return ()
  mrSolveEq' f1 f2 =
    do eqs <- mrFunEqs <$> get
       case lookup (f1,f2) eqs of
         Just True -> return ()
         Just False -> throwError (FunsNotEq f1 f2)
         Nothing -> mrSolveCoInd f1 f2

instance MRSolveEq Comp Comp where
  mrSolveEq' comp1 comp2 =
    do norm1 <- whnfComp comp1
       norm2 <- whnfComp comp2
       mrSolveEq norm1 norm2

instance MRSolveEq CompFun CompFun where
  mrSolveEq' f1 f2 =
    do tp <- compFunInputType f1
       var <- liftSC2 scFreshGlobal "x" tp
       comp1 <- applyCompFun f1 var
       comp2 <- applyCompFun f2 var
       mrSolveEq comp1 comp2

instance MRSolveEq Comp WHNFComp where
  mrSolveEq' comp1 norm2 =
    do norm1 <- whnfComp comp1
       mrSolveEq norm1 norm2

instance MRSolveEq WHNFComp Comp where
  mrSolveEq' norm1 comp2 =
    do norm2 <- whnfComp comp2
       mrSolveEq norm1 norm2

instance MRSolveEq WHNFComp WHNFComp where
  mrSolveEq' (Return t1) (Return t2) =
    -- Returns are equal iff their returned values are
    mrSolveEq t1 t2
  mrSolveEq' (Return t1) Error =
    -- Return is never equal to error
    throwError (ReturnNotError t1)
  mrSolveEq' Error (Return t2) =
    -- Return is never equal to error
    throwError (ReturnNotError t2)
  mrSolveEq' Error Error =
    -- Error trivially equals itself
    return ()
  mrSolveEq' (If cond1 then1 else1) norm2@(If cond2 then2 else2) =
    -- Special case if the two conditions are equal: assert the one condition to
    -- test the then branches and assert its negtion to test the elses
    do eq <- mrTermsEq cond1 cond2
       if eq then
         (withPathCondition cond1 $ mrSolveEq then1 then2) >>
         (withNotPathCondition cond1 $ mrSolveEq else1 else2)
         else
         -- Otherwise, compare the first then and else, under their respective
         -- path conditions, to the whole second computation
         (withPathCondition cond1 $ mrSolveEq then1 norm2) >>
         (withNotPathCondition cond1 $ mrSolveEq else1 norm2)
  mrSolveEq' (If cond1 then1 else1) norm2 =
    -- To compare an if to anything else, compare the then and else, under their
    -- respective path conditions, to the other computation
    (withPathCondition cond1 $ mrSolveEq then1 norm2) >>
    (withNotPathCondition cond1 $ mrSolveEq else1 norm2)
  mrSolveEq' norm1 (If cond2 then2 else2) =
    -- To compare an if to anything else, compare the then and else, under their
    -- respective path conditions, to the other computation
    (withPathCondition cond2 $ mrSolveEq norm1 then2) >>
    (withNotPathCondition cond2 $ mrSolveEq norm1 else2)
  mrSolveEq' comp1@(FunBind f1 args1 mark1 k1) comp2@(FunBind f2 args2 mark2 k2) =
    -- To compare two computations (f1 args1 >>= norm1) and (f2 args2 >>= norm2)
    -- we first test if (f1 args1) and (f2 args2) are equal. If so, we recurse
    -- and compare norm1 and norm2; otherwise, we try unfolding one or the other
    -- of f1 and f2.
    catchErrorEither cmp_funs >>= \ cmp_fun_res ->
    case cmp_fun_res of
      Right () -> mrSolveEq k1 k2
      Left err ->
        mapFailure (MRFailureDisj err) $
        (mrUnfoldFunBind f1 args1 mark1 k1 >>= \c -> mrSolveEq c comp2)
        `mrOr`
        (mrUnfoldFunBind f2 args2 mark2 k2 >>= \c -> mrSolveEq comp1 c)
    where
      cmp_funs =
        do let tp1 = funNameType f1
           let tp2 = funNameType f2
           mrSolveEq (Type tp1) (Type tp2)
           mrSolveEq f1 f2
           zipWithM_ mrSolveEq args1 args2
  mrSolveEq' (FunBind f1 args1 mark1 k1) comp2 =
    -- This case compares a function call to a Return or Error; the only thing
    -- to do is unfold the function call and recurse
    mrUnfoldFunBind f1 args1 mark1 k1 >>= \c -> mrSolveEq c comp2
  mrSolveEq' comp1 (FunBind f2 args2 mark2 k2) =
    -- This case compares a function call to a Return or Error; the only thing
    -- to do is unfold the function call and recurse
    mrUnfoldFunBind f2 args2 mark2 k2 >>= \c -> mrSolveEq comp1 c


----------------------------------------------------------------------
-- * External Entrypoints
----------------------------------------------------------------------

-- | Test two monadic, recursive terms for equivalence
askMRSolver ::
  SharedContext ->
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  Term -> Term -> IO (Maybe MRFailure)

askMRSolver sc smt_conf timeout t1 t2 =
  do tp1 <- scTypeOf sc t1
     tp2 <- scTypeOf sc t2
     true_tm <- scBool sc True
     let init_st = MRState {
           mrSC = sc,
           mrSMTConfig = smt_conf,
           mrSMTTimeout = timeout,
           mrLocalFuns = [],
           mrFunEqs = [],
           mrPathCondition = true_tm
           }
     res <-
       flip evalStateT init_st $ runExceptT $
       do mrSolveEq (Type tp1) (Type tp2)
          let (pi_args, ret_tp) = asPiList tp1
          vars <- mapM (\(x, x_tp) -> liftSC2 scFreshGlobal x x_tp) pi_args
          case asCompMApp ret_tp of
            Just _ -> return ()
            Nothing -> throwError (NotCompFunType tp1)
          t1_app <- liftSC2 scApplyAll t1 vars
          t2_app <- liftSC2 scApplyAll t2 vars
          mrSolveEq (CompTerm t1_app) (CompTerm t2_app)
     case res of
       Left err -> return $ Just err
       Right () -> return Nothing
-}
