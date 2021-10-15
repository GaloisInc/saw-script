{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

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

C |- F e1 ... en >>= k <= F' e1' ... em' >>= k':

* If we have an assumption that forall x1 ... xj, F a1 ... an <= F' a1' .. am',
  prove ei = ai and ei' = ai' and then that C |- k x <= k' x for fresh uvar x

* If we have an assumption that forall x1, ..., xn, F e1'' ... en'' <= m' for
  some ei'' and m', match the ei'' against the ei by instantiating the xj with
  fresh evars, and if this succeeds then recursively prove C |- m' >>= k <= RHS

(We don't do this one right now)
* If we have an assumption that forall x1', ..., xn', m <= F e1'' ... en'' for
  some ei'' and m', match the ei'' against the ei by instantiating the xj with
  fresh evars, and if this succeeds then recursively prove C |- LHS <= m' >>= k'

* If either side is a definition whose unfolding does not contain letrecM, fixM,
  or any related operations, unfold it

* If F and F' have the same return type, add an assumption forall uvars in scope
  that F e1 ... en <= F' e1' ... em' and unfold both sides, recursively proving
  that F_body e1 ... en <= F_body' e1' ... em'. Then also prove k x <= k' x for
  fresh uvar x.

* Otherwise we don't know to "split" one of the sides into a bind whose
  components relate to the two components on the other side, so just fail
-}

module SAWScript.Prover.MRSolver
  (askMRSolver, MRFailure(..), showMRFailure, isCompFunType
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  ) where

import Data.List (findIndex)
import Data.IORef
import System.IO (hPutStrLn, stderr)
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Control.Monad.Trans.Maybe

import qualified Data.IntMap as IntMap
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

import SAWScript.Proof (termToProp)
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
           liftIO (readIORef table_ref) >>= \table ->
           case IntMap.lookup ix table of
             Just ret -> return ret
             Nothing ->
               do ret <- f go t
                  liftIO $ modifyIORef' table_ref (IntMap.insert ix ret)
                  return ret
         go t = f go t
     go term_top

-- | Recursively test if a 'Term' contains @letRecM@
containsLetRecM :: Term -> Bool
containsLetRecM (asGlobalDef -> Just "Prelude.letRecM") = True
containsLetRecM (unwrapTermF -> tf) = any containsLetRecM tf


----------------------------------------------------------------------
-- * MR Solver Term Representation
----------------------------------------------------------------------

-- | A variable used by the MR solver
newtype MRVar = MRVar { unMRVar :: ExtCns Term } deriving (Eq, Show, Ord)

-- | Get the type of an 'MRVar'
mrVarType :: MRVar -> Term
mrVarType = ecType . unMRVar

-- | Names of functions to be used in computations, which are either names bound
-- by letrec to for recursive calls to fixed-points, existential variables, or
-- global named constants
data FunName
  = LetRecName MRVar | EVarFunName MRVar | GlobalName GlobalDef
  deriving (Eq, Ord, Show)

-- | Get the type of a 'FunName'
funNameType :: FunName -> Term
funNameType (LetRecName var) = mrVarType var
funNameType (EVarFunName var) = mrVarType var
funNameType (GlobalName gd) = globalDefType gd

-- | A term specifically known to be of type @sort i@ for some @i@
newtype Type = Type Term deriving Show

-- | A Haskell representation of a @CompM@ in "monadic normal form"
data NormComp
  = ReturnM Term -- ^ A term @returnM a x@
  | ErrorM Term -- ^ A term @errorM a str@
  | Ite Term Comp Comp -- ^ If-then-else computation
  | Either CompFun CompFun Term -- ^ A sum elimination
  | OrM Comp Comp -- ^ an @orM@ computation
  | ExistsM Type CompFun -- ^ an @existsM@ computation
  | ForallM Type CompFun -- ^ a @forallM@ computation
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

-- | If a 'CompFun' contains an explicit lambda-abstraction, then return the
-- textual name bound by that lambda
compFunVarName :: CompFun -> Maybe LocalName
compFunVarName (CompFunTerm (asLambda -> Just (nm, _, _))) = Just nm
compFunVarName (CompFunComp f _) = compFunVarName f
compFunVarName _ = Nothing

-- | If a 'CompFun' contains an explicit lambda-abstraction, then return the
-- input type for it
compFunInputType :: CompFun -> Maybe Type
compFunInputType (CompFunTerm (asLambda -> Just (_, tp, _))) = Just $ Type tp
compFunInputType (CompFunComp f _) = compFunInputType f
compFunInputType _ = Nothing

-- | A computation of type @CompM a@ for some @a@
data Comp = CompTerm Term | CompBind Comp CompFun | CompReturn Term
          deriving Show


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

instance PrettyInCtx MRVar where
  prettyInCtx (MRVar ec) = return $ ppName $ ecName ec

instance PrettyInCtx FunName where
  prettyInCtx (LetRecName var) = prettyInCtx var
  prettyInCtx (EVarFunName var) = prettyInCtx var
  prettyInCtx (GlobalName i) = return $ viaShow i

instance PrettyInCtx Comp where
  prettyInCtx (CompTerm t) = prettyInCtx t
  prettyInCtx (CompBind c f) =
    prettyAppList [prettyInCtx c, return ">>=", prettyInCtx f]
  prettyInCtx (CompReturn t) =
    prettyAppList [ return "returnM", return "_", parens <$> prettyInCtx t]

instance PrettyInCtx CompFun where
  prettyInCtx (CompFunTerm t) = prettyInCtx t
  prettyInCtx CompFunReturn = return "returnM"
  prettyInCtx (CompFunComp f g) =
    prettyAppList [prettyInCtx f, return ">=>", prettyInCtx g]

instance PrettyInCtx NormComp where
  prettyInCtx (ReturnM t) =
    prettyAppList [return "returnM", return "_", parens <$> prettyInCtx t]
  prettyInCtx (ErrorM str) =
    prettyAppList [return "errorM", return "_", parens <$> prettyInCtx str]
  prettyInCtx (Ite cond t1 t2) =
    prettyAppList [return "ite", return "_", prettyInCtx cond,
                   parens <$> prettyInCtx t1, parens <$> prettyInCtx t2]
  prettyInCtx (Either f g eith) =
    prettyAppList [return "either", return "_", return "_", return "_",
                   prettyInCtx f, prettyInCtx g, prettyInCtx eith]
  prettyInCtx (OrM t1 t2) =
    prettyAppList [return "orM", return "_",
                   parens <$> prettyInCtx t1, parens <$> prettyInCtx t2]
  prettyInCtx (ExistsM tp f) =
    prettyAppList [return "existsM", prettyInCtx tp, return "_",
                   parens <$> prettyInCtx f]
  prettyInCtx (ForallM tp f) =
    prettyAppList [return "forallM", prettyInCtx tp, return "_",
                   parens <$> prettyInCtx f]
  prettyInCtx (FunBind f [] k) =
    prettyAppList [prettyInCtx f, return ">>=", prettyInCtx k]
  prettyInCtx (FunBind f args k) =
    prettyAppList
    [parens <$> prettyAppList (prettyInCtx f : map prettyInCtx args),
     return ">>=", prettyInCtx k]


----------------------------------------------------------------------
-- * Lifting MR Solver Terms
----------------------------------------------------------------------

-- | A term-like object is one that supports lifting and substitution
class TermLike a where
  liftTermLike :: MonadTerm m => DeBruijnIndex -> DeBruijnIndex -> a -> m a
  substTermLike :: MonadTerm m => DeBruijnIndex -> [Term] -> a -> m a

instance (TermLike a, TermLike b) => TermLike (a,b) where
  liftTermLike n i (a,b) = (,) <$> liftTermLike n i a <*> liftTermLike n i b
  substTermLike n s (a,b) = (,) <$> substTermLike n s a <*> substTermLike n s b

instance TermLike a => TermLike [a] where
  liftTermLike n i l = mapM (liftTermLike n i) l
  substTermLike n s l = mapM (substTermLike n s) l

instance TermLike Term where
  liftTermLike = liftTerm
  substTermLike = substTerm

instance TermLike Type where
  liftTermLike n i (Type tp) = Type <$> liftTerm n i tp
  substTermLike n s (Type tp) = Type <$> substTerm n s tp

instance TermLike NormComp where
  liftTermLike n i (ReturnM t) = ReturnM <$> liftTermLike n i t
  liftTermLike n i (ErrorM str) = ErrorM <$> liftTermLike n i str
  liftTermLike n i (Ite cond t1 t2) =
    Ite <$> liftTermLike n i cond <*> liftTermLike n i t1 <*> liftTermLike n i t2
  liftTermLike n i (Either f g eith) =
    Either <$> liftTermLike n i f <*> liftTermLike n i g <*> liftTermLike n i eith
  liftTermLike n i (OrM t1 t2) = OrM <$> liftTermLike n i t1 <*> liftTermLike n i t2
  liftTermLike n i (ExistsM tp f) =
    ExistsM <$> liftTermLike n i tp <*> liftTermLike n i f
  liftTermLike n i (ForallM tp f) =
    ForallM <$> liftTermLike n i tp <*> liftTermLike n i f
  liftTermLike n i (FunBind nm args f) =
    FunBind nm <$> mapM (liftTermLike n i) args <*> liftTermLike n i f

  substTermLike n s (ReturnM t) = ReturnM <$> substTermLike n s t
  substTermLike n s (ErrorM str) = ErrorM <$> substTermLike n s str
  substTermLike n s (Ite cond t1 t2) =
    Ite <$> substTermLike n s cond <*> substTermLike n s t1
    <*> substTermLike n s t2
  substTermLike n s (Either f g eith) =
    Either <$> substTermLike n s f <*> substTermLike n s g
    <*> substTermLike n s eith
  substTermLike n s (OrM t1 t2) =
    OrM <$> substTermLike n s t1 <*> substTermLike n s t2
  substTermLike n s (ExistsM tp f) =
    ExistsM <$> substTermLike n s tp <*> substTermLike n s f
  substTermLike n s (ForallM tp f) =
    ForallM <$> substTermLike n s tp <*> substTermLike n s f
  substTermLike n s (FunBind nm args f) =
    FunBind nm <$> mapM (substTermLike n s) args <*> substTermLike n s f

instance TermLike CompFun where
  liftTermLike n i (CompFunTerm t) = CompFunTerm <$> liftTermLike n i t
  liftTermLike _ _ CompFunReturn = return CompFunReturn
  liftTermLike n i (CompFunComp f g) =
    CompFunComp <$> liftTermLike n i f <*> liftTermLike n i g

  substTermLike n s (CompFunTerm t) = CompFunTerm <$> substTermLike n s t
  substTermLike _ _ CompFunReturn = return CompFunReturn
  substTermLike n s (CompFunComp f g) =
    CompFunComp <$> substTermLike n s f <*> substTermLike n s g

instance TermLike Comp where
  liftTermLike n i (CompTerm t) = CompTerm <$> liftTermLike n i t
  liftTermLike n i (CompBind m f) =
    CompBind <$> liftTermLike n i m <*> liftTermLike n i f
  liftTermLike n i (CompReturn t) = CompReturn <$> liftTermLike n i t
  substTermLike n s (CompTerm t) = CompTerm <$> substTermLike n s t
  substTermLike n s (CompBind m f) =
    CompBind <$> substTermLike n s m <*> substTermLike n s f
  substTermLike n s (CompReturn t) = CompReturn <$> substTermLike n s t


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
    ppWithPrefixSep "When proving refinement:" m1 "<=" m2
  prettyInCtx (FailCtxMNF t) =
    group <$> nest 2 <$> vsepM [return "When normalizing computation:",
                                prettyInCtx t]

instance PrettyInCtx MRFailure where
  prettyInCtx (TermsNotEq t1 t2) =
    ppWithPrefixSep "Could not prove terms equal:" t1 "and" t2
  prettyInCtx (TypesNotEq tp1 tp2) =
    ppWithPrefixSep "Types not equal:" tp1 "and" tp2
  prettyInCtx (CompsDoNotRefine m1 m2) =
    ppWithPrefixSep "Could not prove refinement: " m1 "<=" m2
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

-- | An assumption that a named function refines some specificaiton. This has
-- the form
--
-- > forall x1, ..., xn. F e1 ... ek <= m
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
  fassumpRHS :: NormComp }

-- | State maintained by MR. Solver
data MRState = MRState {
  -- | Global shared context for building terms, etc.
  mrSC :: SharedContext,
  -- | Global SMT configuration for the duration of the MR. Solver call
  mrSMTConfig :: SBV.SMTConfig,
  -- | SMT timeout for SMT calls made by Mr. Solver
  mrSMTTimeout :: Maybe Integer,
  -- | The context of universal variables, which are free SAW core variables, in
  -- order from innermost to outermost, i.e., where element @0@ corresponds to
  -- deBruijn index @0@
  mrUVars :: [(LocalName,Type)],
  -- | The existential and letrec-bound variables
  mrVars :: MRVarMap,
  -- | The current assumptions of function refinement
  mrFunAssumps :: Map FunName FunAssump,
  -- | The current assumptions, which are conjoined into a single Boolean term
  mrAssumptions :: Term,
  -- | The debug level, which controls debug printing
  mrDebugLevel :: Int
}

-- | Build a default, empty state from SMT configuration parameters and a set of
-- function refinement assumptions
mkMRState :: SharedContext -> Map FunName FunAssump -> SBV.SMTConfig ->
             Maybe Integer -> Int -> IO MRState
mkMRState sc fun_assumps smt_config timeout dlvl =
  scBool sc True >>= \true_tm ->
  return $ MRState { mrSC = sc, mrSMTConfig = smt_config,
                     mrSMTTimeout = timeout, mrUVars = [], mrVars = Map.empty,
                     mrFunAssumps = fun_assumps, mrAssumptions = true_tm,
                     mrDebugLevel = dlvl }

-- | Mr. Monad, the monad used by MR. Solver, which is the state-exception monad
newtype MRM a = MRM { unMRM :: StateT MRState (ExceptT MRFailure IO) a }
              deriving (Functor, Applicative, Monad, MonadIO,
                        MonadState MRState, MonadError MRFailure)

instance MonadTerm MRM where
  mkTermF = liftSC1 scTermF
  liftTerm = liftSC3 incVars
  whnfTerm = liftSC1 scWhnf
  substTerm = liftSC3 instantiateVarList

-- | Run an 'MRM' computation and return a result or an error
runMRM :: MRState -> MRM a -> IO (Either MRFailure a)
runMRM init_st m = runExceptT $ flip evalStateT init_st $ unMRM m

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

{-
-- | Lift a nullary SharedTerm computation into 'MRM'
liftSC0 :: (SharedContext -> IO a) -> MRM a
liftSC0 f = (mrSC <$> get) >>= \sc -> liftIO (f sc)
-}

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

-- | Apply a 'Term' to a list of arguments and beta-reduce in Mr. Monad
mrApplyAll :: Term -> [Term] -> MRM Term
mrApplyAll f args = liftSC2 scApplyAll f args >>= liftSC1 betaNormalize

-- | Get the current context of uvars as a list of variable names and their
-- types as SAW core 'Term's, with the least recently bound uvar first, i.e., in
-- the order as seen "from the outside"
mrUVarCtx :: MRM [(LocalName,Term)]
mrUVarCtx = reverse <$> map (\(nm,Type tp) -> (nm,tp)) <$> mrUVars <$> get

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
mrFunOutType ((asPiList . funNameType) -> (vars, asCompM -> Just tp)) args
  | length vars == length args =
    substTermLike 0 args tp
mrFunOutType _ _ =
  -- NOTE: this is an error because we should only ever call mrFunOutType with a
  -- well-formed application at a CompM type
  error "mrFunOutType"

-- | Run a MR Solver computation in a context extended with a universal
-- variable, which is passed as a 'Term' to the sub-computation
withUVar :: LocalName -> Type -> (Term -> MRM a) -> MRM a
withUVar nm tp m =
  mapFailure (MRFailureLocalVar nm) $
  do st <- get
     put (st { mrUVars = (nm,tp) : mrUVars st })
     ret <- liftSC1 scLocalVar 0 >>= m
     modify (\st' -> st' { mrUVars = mrUVars st })
     return ret

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
    substTerm 0 vars tp >>= \tp' ->
    withUVar nm (Type tp') $ \var -> helper (var:vars) ctx m

-- | Build 'Term's for all the uvars currently in scope, ordered from least to
-- most recently bound
getAllUVarTerms :: MRM [Term]
getAllUVarTerms =
  (length <$> mrUVars <$> get) >>= \len ->
  mapM (liftSC1 scLocalVar) [len-1, len-2 .. 0]

-- | Lambda-abstract all the current uvars out of a 'Term', with the least
-- recently bound variable being abstracted first
lambdaUVarsM :: Term -> MRM Term
lambdaUVarsM t = mrUVarCtx >>= \ctx -> liftSC2 scLambdaList ctx t

-- | Pi-abstract all the current uvars out of a 'Term', with the least recently
-- bound variable being abstracted first
piUVarsM :: Term -> MRM Term
piUVarsM t = mrUVarCtx >>= \ctx -> liftSC2 scPiList ctx t

-- | Convert an 'MRVar' to a 'Term', applying it to all the uvars in scope
mrVarTerm :: MRVar -> MRM Term
mrVarTerm (MRVar ec) =
  do var_tm <- liftSC1 scExtCns ec
     vars <- getAllUVarTerms
     liftSC2 scApplyAll var_tm vars

-- | Get the 'VarInfo' associated with a 'MRVar'
mrVarInfo :: MRVar -> MRM (Maybe MRVarInfo)
mrVarInfo var = Map.lookup var <$> mrVars <$> get

-- | Convert an 'ExtCns' to a 'FunName'
extCnsToFunName :: ExtCns Term -> MRM FunName
extCnsToFunName ec = let var = MRVar ec in mrVarInfo var >>= \case
  Just (EVarInfo _) -> return $ EVarFunName var
  Just (FunVarInfo _) -> return $ LetRecName var
  Nothing
    | Just glob <- asTypedGlobalDef (Unshared $ FTermF $ ExtCns ec) ->
      return $ GlobalName glob
  _ -> error "extCnsToFunName: unreachable"

-- | Get the body of a function @f@ if it has one
mrFunNameBody :: FunName -> MRM (Maybe Term)
mrFunNameBody (LetRecName var) =
  mrVarInfo var >>= \case
  Just (FunVarInfo body) -> return $ Just body
  _ -> error "mrFunBody: unknown letrec var"
mrFunNameBody (GlobalName glob) = return $ globalDefBody glob
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
  (asTypedGlobalDef -> Just gdef) ->
    case globalDefBody gdef of
      _ | f == GlobalName gdef -> return True
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
  st { mrVars =
         Map.alter (\case
                       Just _ -> error "mrSetVarInfo"
                       Nothing -> Just info)
         var (mrVars st) }

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
  do var_map <- mrVars <$> get
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
  do var_map <- mrVars <$> get
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

-- | Look up the 'FunAssump' for a 'FunName', if there is one
mrGetFunAssump :: FunName -> MRM (Maybe FunAssump)
mrGetFunAssump nm = Map.lookup nm <$> mrFunAssumps <$> get

-- | Run a computation under the additional assumption that a named function
-- applied to a list of arguments refines a given right-hand side, all of which
-- are 'Term's that can have the current uvars free
withFunAssump :: FunName -> [Term] -> NormComp -> MRM a -> MRM a
withFunAssump fname args rhs m =
  do ctx <- mrUVarCtx
     assumps <- mrFunAssumps <$> get
     let assumps' = Map.insert fname (FunAssump ctx args rhs) assumps
     modify (\s -> s { mrFunAssumps = assumps' })
     ret <- m
     modify (\s -> s { mrFunAssumps = assumps })
     return ret

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
  do assumps <- mrAssumptions <$> get
     assumps' <- liftSC2 scAnd phi assumps
     modify (\s -> s { mrAssumptions = assumps' })
     ret <- m
     modify (\s -> s { mrAssumptions = assumps })
     return ret

-- | Print a 'String' if the debug level is at least the supplied 'Int'
debugPrint :: Int -> String -> MRM ()
debugPrint i str =
  (mrDebugLevel <$> get) >>= \lvl ->
  if lvl >= i then liftIO (hPutStrLn stderr str) else return ()

-- | Print a document if the debug level is at least the supplied 'Int'
debugPretty :: Int -> SawDoc -> MRM ()
debugPretty i pp = debugPrint i $ renderSawDoc defaultPPOpts pp

-- | Pretty-print an object in the current context if the current debug level is
-- at least the supplied 'Int'
debugPrettyInCtx :: PrettyInCtx a => Int -> a -> MRM ()
debugPrettyInCtx i a =
  (mrUVars <$> get) >>= \ctx -> debugPrint i (showInCtx (map fst ctx) a)

-- | Pretty-print an object relative to the current context
mrPPInCtx :: PrettyInCtx a => a -> MRM SawDoc
mrPPInCtx a =
  runReader (prettyInCtx a) <$> map fst <$> mrUVars <$> get

-- | Pretty-print the result of 'ppWithPrefixSep' relative to the current uvar
-- context to 'stderr' if the debug level is at least the 'Int' provided
mrDebugPPPrefixSep :: PrettyInCtx a => Int -> String -> a -> String -> a ->
                      MRM ()
mrDebugPPPrefixSep i pre a1 sp a2 =
  (mrUVars <$> get) >>= \ctx ->
  debugPretty i $
  flip runReader (map fst ctx) (group <$> nest 2 <$>
                                ppWithPrefixSep pre a1 sp a2)


----------------------------------------------------------------------
-- * Calling Out to SMT
----------------------------------------------------------------------

-- | Test if a closed Boolean term is "provable", i.e., its negation is
-- unsatisfiable, using an SMT solver. By "closed" we mean that it contains no
-- uvars or 'MRVar's.
mrProvableRaw :: Term -> MRM Bool
mrProvableRaw prop_term =
  do smt_conf <- mrSMTConfig <$> get
     timeout <- mrSMTTimeout <$> get
     prop <- liftSC1 termToProp prop_term
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

-- | Build a Boolean 'Term' stating that two 'Term's are equal. This is like
-- 'scEq' except that it works on open terms.
mrEq :: Term -> Term -> MRM Term
mrEq t1 t2 = mrTypeOf t1 >>= \tp -> mrEq' tp t1 t2

-- | Build a Boolean 'Term' stating that the second and third 'Term' arguments
-- are equal, where the first 'Term' gives their type (which we assume is the
-- same for both). This is like 'scEq' except that it works on open terms.
mrEq' :: Term -> Term -> Term -> MRM Term
mrEq' (asDataType -> Just (pn, [])) t1 t2
  | primName pn == "Prelude.Nat" = liftSC2 scEqualNat t1 t2
mrEq' (asBoolType -> Just _) t1 t2 = liftSC2 scBoolEq t1 t2
mrEq' (asIntegerType -> Just _) t1 t2 = liftSC2 scIntEq t1 t2
mrEq' (asVectorType -> Just (n, asBoolType -> Just ())) t1 t2 =
  liftSC3 scBvEq n t1 t2
mrEq' _ _ _ = error "mrEq': unsupported type"

-- | A "simple" strategy for proving equality between two terms, which we assume
-- are of the same type. This strategy first checks if either side is an
-- uninstantiated evar, in which case it set that evar to the other side. If
-- not, it builds an equality proposition by applying the supplied function to
-- both sides, and passes this proposition to an SMT solver.
mrProveEqSimple :: (Term -> Term -> MRM Term) -> MRVarMap -> Term -> Term ->
                   MRM ()

-- If t1 is an instantiated evar, substitute and recurse
mrProveEqSimple eqf var_map (asEVarApp var_map -> Just (_, args, Just f)) t2 =
  mrApplyAll f args >>= \t1' -> mrProveEqSimple eqf var_map t1' t2

-- If t1 is an uninstantiated evar, instantiate it with t2
mrProveEqSimple _ var_map t1@(asEVarApp var_map ->
                              Just (evar, args, Nothing)) t2 =
  do t2' <- mrSubstEVars t2
     success <- mrTrySetAppliedEVar evar args t2'
     if success then return () else throwError (TermsNotEq t1 t2)

-- If t2 is an instantiated evar, substitute and recurse
mrProveEqSimple eqf var_map t1 (asEVarApp var_map -> Just (_, args, Just f)) =
  mrApplyAll f args >>= \t2' -> mrProveEqSimple eqf var_map t1 t2'

-- If t2 is an uninstantiated evar, instantiate it with t1
mrProveEqSimple _ var_map t1 t2@(asEVarApp var_map ->
                                 Just (evar, args, Nothing)) =
  do t1' <- mrSubstEVars t1
     success <- mrTrySetAppliedEVar evar args t1'
     if success then return () else throwError (TermsNotEq t1 t2)

-- Otherwise, try to prove both sides are equal. The use of mrSubstEVars instead
-- of mrSubstEVarsStrict means that we allow evars in the terms we send to the
-- SMT solver, but we treat them as uvars.
mrProveEqSimple eqf _ t1 t2 =
  do t1' <- mrSubstEVars t1
     t2' <- mrSubstEVars t2
     prop <- eqf t1' t2'
     success <- mrProvable prop
     if success then return () else
       throwError (TermsNotEq t1 t2)


-- | Prove that two terms are equal, instantiating evars if necessary, or
-- throwing an error if this is not possible
mrProveEq :: Term -> Term -> MRM ()
mrProveEq t1_top t2_top =
  (do mrDebugPPPrefixSep 1 "mrProveEq" t1_top "==" t2_top
      tp <- mrTypeOf t1_top
      varmap <- mrVars <$> get
      proveEq varmap tp t1_top t2_top)
  where
    proveEq :: Map MRVar MRVarInfo -> Term -> Term -> Term -> MRM ()
    proveEq var_map (asDataType -> Just (pn, [])) t1 t2
      | primName pn == "Prelude.Nat" =
        mrProveEqSimple (liftSC2 scEqualNat) var_map t1 t2
    proveEq var_map (asVectorType -> Just (n, asBoolType -> Just ())) t1 t2 =
      -- FIXME: make a better solver for bitvector equalities
      mrProveEqSimple (liftSC3 scBvEq n) var_map t1 t2
    proveEq var_map (asBoolType -> Just _) t1 t2 =
      mrProveEqSimple (liftSC2 scBoolEq) var_map t1 t2
    proveEq var_map (asIntegerType -> Just _) t1 t2 =
      mrProveEqSimple (liftSC2 scIntEq) var_map t1 t2
    proveEq _ _ t1 t2 =
      -- As a fallback, for types we can't handle, just check convertibility
      mrConvertible t1 t2 >>= \case
      True -> return ()
      False -> throwError (TermsNotEq t1 t2)


----------------------------------------------------------------------
-- * Normalizing and Matching on Terms
----------------------------------------------------------------------

-- | Match a type as being of the form @CompM a@ for some @a@
asCompM :: Term -> Maybe Term
asCompM (asApp -> Just (isGlobalDef "Prelude.CompM" -> Just (), tp)) =
  return tp
asCompM _ = fail "not a CompM type!"

-- | Test if a type is a monadic function type of 0 or more arguments
isCompFunType :: Term -> Bool
isCompFunType (asPiList -> (_, asCompM -> Just _)) = True
isCompFunType _ = False

-- | Pattern-match on a @LetRecTypes@ list in normal form and return a list of
-- the types it specifies, each in normal form and with uvars abstracted out
asLRTList :: Term -> MRM [Term]
asLRTList (asCtor -> Just (primName -> "Prelude.LRT_Nil", [])) =
  return []
asLRTList (asCtor -> Just (primName -> "Prelude.LRT_Cons", [lrt, lrts])) =
  do tp <- liftSC2 scGlobalApply "Prelude.lrtToType" [lrt]
     tp_norm_closed <- liftSC1 scWhnf tp >>= piUVarsM
     (tp_norm_closed :) <$> asLRTList lrts
asLRTList t = throwError (MalformedLetRecTypes t)

-- | Match a right-nested series of pairs. This is similar to 'asTupleValue'
-- except that it expects a unit value to always be at the end.
asNestedPairs :: Recognizer Term [Term]
asNestedPairs (asPairValue -> Just (x, asNestedPairs -> Just xs)) = Just (x:xs)
asNestedPairs (asFTermF -> Just UnitValue) = Just []
asNestedPairs _ = Nothing

-- | Normalize a 'Term' of monadic type to monadic normal form
normCompTerm :: Term -> MRM NormComp
normCompTerm = normComp . CompTerm

-- | Normalize a computation to monadic normal form, assuming any 'Term's it
-- contains have already been normalized with respect to beta and projections
-- (but constants need not be unfolded)
normComp :: Comp -> MRM NormComp
normComp (CompReturn t) = return $ ReturnM t
normComp (CompBind m f) =
  do norm <- normComp m
     normBind norm f
normComp (CompTerm t) =
  withFailureCtx (FailCtxMNF t) $
  case asApplyAll t of
    (isGlobalDef "Prelude.returnM" -> Just (), [_, x]) ->
      return $ ReturnM x
    (isGlobalDef "Prelude.bindM" -> Just (), [_, _, m, f]) ->
      do norm <- normComp (CompTerm m)
         normBind norm (CompFunTerm f)
    (isGlobalDef "Prelude.errorM" -> Just (), [_, str]) ->
      return (ErrorM str)
    (isGlobalDef "Prelude.ite" -> Just (), [_, cond, then_tm, else_tm]) ->
      return $ Ite cond (CompTerm then_tm) (CompTerm else_tm)
    (isGlobalDef "Prelude.either" -> Just (), [_, _, _, f, g, eith]) ->
      return $ Either (CompFunTerm f) (CompFunTerm g) eith
    (isGlobalDef "Prelude.orM" -> Just (), [_, _, m1, m2]) ->
      return $ OrM (CompTerm m1) (CompTerm m2)
    (isGlobalDef "Prelude.existsM" -> Just (), [tp, _, body_tm]) ->
      return $ ExistsM (Type tp) (CompFunTerm body_tm)
    (isGlobalDef "Prelude.forallM" -> Just (), [tp, _, body_tm]) ->
      return $ ForallM (Type tp) (CompFunTerm body_tm)
    (isGlobalDef "Prelude.letRecM" -> Just (), [lrts, _, defs_f, body_f]) ->
      do
        -- First, make fresh function constants for all the bound functions,
        -- using the names bound by body_f and just "F" if those run out
        let fun_var_names =
              map fst (fst $ asLambdaList body_f) ++ repeat "F"
        fun_tps <- asLRTList lrts
        funs <- zipWithM mrFreshVar fun_var_names fun_tps
        fun_tms <- mapM mrVarTerm funs

        -- Next, apply the definition function defs_f to our function vars,
        -- yielding the definitions of the individual letrec-bound functions in
        -- terms of the new function constants
        defs_tm <- mrApplyAll defs_f fun_tms
        defs <- case asNestedPairs defs_tm of
          Just defs -> return defs
          Nothing -> throwError (MalformedDefsFun defs_f)

        -- Remember the body associated with each fresh function constant
        zipWithM_ (\f body ->
                    lambdaUVarsM body >>= \cl_body ->
                    mrSetVarInfo f (FunVarInfo cl_body)) funs defs

        -- Finally, apply the body function to our function vars and recursively
        -- normalize the resulting computation
        body_tm <- mrApplyAll body_f fun_tms
        normComp (CompTerm body_tm)

    -- Only unfold constants that are not recursive functions, i.e., whose
    -- bodies do not contain letrecs
    {- FIXME: this should be handled by mrRefines; we want it to be handled there
       so that we use refinement assumptions before unfolding constants, to give
       the user control over refinement proofs
    ((asConstant -> Just (_, body)), args)
      | not (containsLetRecM body) ->
        mrApplyAll body args >>= normCompTerm
    -}

    -- For an ExtCns, we have to check what sort of variable it is
    -- FIXME: substitute for evars if they have been instantiated
    ((asExtCns -> Just ec), args) ->
      do fun_name <- extCnsToFunName ec
         return $ FunBind fun_name args CompFunReturn

    ((asTypedGlobalDef -> Just gdef), args) ->
      return $ FunBind (GlobalName gdef) args CompFunReturn

    _ -> throwError (MalformedComp t)


-- | Bind a computation in whnf with a function, and normalize
normBind :: NormComp -> CompFun -> MRM NormComp
normBind (ReturnM t) k = applyNormCompFun k t
normBind (ErrorM msg) _ = return (ErrorM msg)
normBind (Ite cond comp1 comp2) k =
  return $ Ite cond (CompBind comp1 k) (CompBind comp2 k)
normBind (Either f g t) k =
  return $ Either (CompFunComp f k) (CompFunComp g k) t
normBind (OrM comp1 comp2) k =
  return $ OrM (CompBind comp1 k) (CompBind comp2 k)
normBind (ExistsM tp f) k = return $ ExistsM tp (CompFunComp f k)
normBind (ForallM tp f) k = return $ ForallM tp (CompFunComp f k)
normBind (FunBind f args k1) k2 =
  return $ FunBind f args (CompFunComp k1 k2)

-- | Bind a 'Term' for a computation with a function and normalize
normBindTerm :: Term -> CompFun -> MRM NormComp
normBindTerm t f = normCompTerm t >>= \m -> normBind m f

-- | Apply a computation function to a term argument to get a computation
applyCompFun :: CompFun -> Term -> MRM Comp
applyCompFun (CompFunComp f g) t =
  -- (f >=> g) t == f t >>= g
  do comp <- applyCompFun f t
     return $ CompBind comp g
applyCompFun CompFunReturn t =
  return $ CompReturn t
applyCompFun (CompFunTerm f) t = CompTerm <$> mrApplyAll f [t]

-- | Apply a 'CompFun' to a term and normalize the resulting computation
applyNormCompFun :: CompFun -> Term -> MRM NormComp
applyNormCompFun f arg = applyCompFun f arg >>= normComp

-- | Apply a 'Comp

{- FIXME: do these go away?
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
-}


----------------------------------------------------------------------
-- * Mr Solver Himself (He Identifies as Male)
----------------------------------------------------------------------

-- | An object that can be converted to a normalized computation
class ToNormComp a where
  toNormComp :: a -> MRM NormComp

instance ToNormComp NormComp where
  toNormComp = return
instance ToNormComp Comp where
  toNormComp = normComp
instance ToNormComp Term where
  toNormComp = normComp . CompTerm

-- | Prove that the left-hand computation refines the right-hand one. See the
-- rules described at the beginning of this module.
mrRefines :: (ToNormComp a, ToNormComp b) => a -> b -> MRM ()
mrRefines t1 t2 =
  do m1 <- toNormComp t1
     m2 <- toNormComp t2
     mrDebugPPPrefixSep 1 "mrRefines" m1 "<=" m2
     withFailureCtx (FailCtxRefines m1 m2) $ mrRefines' m1 m2

-- | The main implementation of 'mrRefines'
mrRefines' :: NormComp -> NormComp -> MRM ()
mrRefines' (ReturnM e1) (ReturnM e2) = mrProveEq e1 e2
mrRefines' (ErrorM _) (ErrorM _) = return ()
mrRefines' (ReturnM e) (ErrorM _) = throwError (ReturnNotError e)
mrRefines' (ErrorM _) (ReturnM e) = throwError (ReturnNotError e)
mrRefines' (Ite cond1 m1 m1') m2_all@(Ite cond2 m2 m2') =
  liftSC1 scNot cond1 >>= \not_cond1 ->
  (mrEq cond1 cond2 >>= mrProvable) >>= \case
  True ->
    -- If we can prove cond1 == cond2, then we just need to prove m1 <= m2 and
    -- m1' <= m2'; further, we need only add assumptions about cond1, because it
    -- is provably equal to cond2
    withAssumption cond1 (mrRefines m1 m2) >>
    withAssumption not_cond1 (mrRefines m1' m2')
  False ->
    -- Otherwise, prove each branch of the LHS refines the whole RHS
    withAssumption cond1 (mrRefines m1 m2_all) >>
    withAssumption not_cond1 (mrRefines m1' m2_all)
mrRefines' (Ite cond1 m1 m1') m2 =
  do not_cond1 <- liftSC1 scNot cond1
     withAssumption cond1 (mrRefines m1 m2)
     withAssumption not_cond1 (mrRefines m1' m2)
mrRefines' m1 (Ite cond2 m2 m2') =
  do not_cond2 <- liftSC1 scNot cond2
     withAssumption cond2 (mrRefines m1 m2)
     withAssumption not_cond2 (mrRefines m1 m2')
-- FIXME: handle sum elimination
-- mrRefines (Either f1 g1 e1) (Either f2 g2 e2) =
mrRefines' m1 (ForallM tp f2) =
  let nm = maybe "x" id (compFunVarName f2) in
  withUVarLift nm tp (m1,f2) $ \x (m1',f2') ->
  applyNormCompFun f2' x >>= \m2' ->
  mrRefines m1' m2'
mrRefines' (ExistsM tp f1) m2 =
  let nm = maybe "x" id (compFunVarName f1) in
  withUVarLift nm tp (f1,m2) $ \x (f1',m2') ->
  applyNormCompFun f1' x >>= \m1' ->
  mrRefines m1' m2'
mrRefines' m1 (OrM m2 m2') =
  mrOr (mrRefines m1 m2) (mrRefines m1 m2')
mrRefines' (OrM m1 m1') m2 =
  mrRefines m1 m2 >> mrRefines m1' m2
     
-- FIXME: the following cases don't work unless we either allow evars to be set
-- to NormComps or we can turn NormComps back into terms
mrRefines' m1@(FunBind (EVarFunName _) _ _) m2 =
  throwError (CompsDoNotRefine m1 m2)
mrRefines' m1 m2@(FunBind (EVarFunName _) _ _) =
  throwError (CompsDoNotRefine m1 m2)
{-
mrRefines' (FunBind (EVarFunName evar) args CompFunReturn) m2 =
  mrGetEVar evar >>= \case
  Just f ->
    (mrApplyAll f args >>= normCompTerm) >>= \m1' ->
    mrRefines m1' m2
  Nothing -> mrTrySetAppliedEVar evar args m2
-}

mrRefines' (FunBind f args1 k1) (FunBind f' args2 k2)
  | f == f' && length args1 == length args2 =
    zipWithM_ mrProveEq args1 args2 >>
    mrRefinesFun k1 k2

mrRefines' m1@(FunBind f1 args1 k1) m2@(FunBind f2 args2 k2) =
  mrFunOutType f1 args1 >>= \tp1 ->
  mrFunOutType f2 args2 >>= \tp2 ->
  mrConvertible tp1 tp2 >>= \tps_eq ->
  mrFunBodyRecInfo f1 args1 >>= \maybe_f1_body ->
  mrFunBodyRecInfo f2 args2 >>= \maybe_f2_body ->
  mrGetFunAssump f1 >>= \case

  -- If we have an assumption that f1 args' refines some rhs, then prove that
  -- args1 = args' and then that rhs refines m2
  Just fassump ->
    do (assump_args, assump_rhs) <- instantiateFunAssump fassump
       zipWithM_ mrProveEq assump_args args1
       m1' <- normBind assump_rhs k1
       mrRefines m1' m2

  -- If f1 unfolds and is not recursive in itself, unfold it and recurse
  _ | Just (f1_body, False) <- maybe_f1_body ->
      normBindTerm f1_body k1 >>= \m1' -> mrRefines m1' m2

  -- If f2 unfolds and is not recursive in itself, unfold it and recurse
  _ | Just (f2_body, False) <- maybe_f2_body ->
      normBindTerm f2_body k2 >>= \m2' -> mrRefines m1 m2'

  -- If we do not already have an assumption that f1 refines some specification,
  -- and both f1 and f2 are recursive but have the same return type, then try to
  -- coinductively prove that f1 args1 <= f2 args2 under the assumption that f1
  -- args1 <= f2 args2, and then try to prove that k1 <= k2
  Nothing
    | tps_eq
    , Just (f1_body, _) <- maybe_f1_body
    , Just (f2_body, _) <- maybe_f2_body ->
      do withFunAssump f1 args1 (FunBind f2 args2 CompFunReturn) $
           mrRefines f1_body f2_body
         mrRefinesFun k1 k2

  -- If we cannot line up f1 and f2, then making progress here would require us
  -- to somehow split either m1 or m2 into some bind m' >>= k' such that m' is
  -- related to the function call on the other side and k' is related to the
  -- continuation on the other side, but we don't know how to do that, so give
  -- up
  Nothing ->
    throwError (CompsDoNotRefine m1 m2)

{- FIXME: handle FunBind on just one side
mrRefines' m1@(FunBind f@(GlobalName _) args k1) m2 =
  mrGetFunAssump f >>= \case
  Just fassump ->
    -- If we have an assumption that f args' refines some rhs, then prove that
    -- args = args' and then that rhs refines m2
    do (assump_args, assump_rhs) <- instantiateFunAssump fassump
       zipWithM_ mrProveEq assump_args args
       m1' <- normBind assump_rhs k1
       mrRefines m1' m2
  Nothing ->
    -- We don't want to do inter-procedural proofs, so if we don't know anything
    -- about f already then give up
    throwError (CompsDoNotRefine m1 m2)
-}


mrRefines' m1@(FunBind f1 args1 k1) m2 =
  mrGetFunAssump f1 >>= \case

  -- If we have an assumption that f1 args' refines some rhs, then prove that
  -- args1 = args' and then that rhs refines m2
  Just fassump ->
    do (assump_args, assump_rhs) <- instantiateFunAssump fassump
       zipWithM_ mrProveEq assump_args args1
       m1' <- normBind assump_rhs k1
       mrRefines m1' m2

  -- Otherwise, see if we can unfold f1
  Nothing ->
    mrFunBodyRecInfo f1 args1 >>= \case

    -- If f1 unfolds and is not recursive in itself, unfold it and recurse
    Just (f1_body, False) ->
      normBindTerm f1_body k1 >>= \m1' -> mrRefines m1' m2

    -- Otherwise we would have to somehow split m2 into some computation of the
    -- form m2' >>= k2 where f1 args1 <= m2' and k1 <= k2, but we don't know how
    -- to do this splitting, so give up
    _ ->
      throwError (CompsDoNotRefine m1 m2)


mrRefines' m1 m2@(FunBind f2 args2 k2) =
  mrFunBodyRecInfo f2 args2 >>= \case

  -- If f2 unfolds and is not recursive in itself, unfold it and recurse
  Just (f2_body, False) ->
    normBindTerm f2_body k2 >>= \m2' -> mrRefines m1 m2'

  -- If f2 unfolds but is recursive, and k2 is the trivial continuation, meaning
  -- m2 is just f2 args2, use the law of coinduction to prove m1 <= f2 args2 by
  -- proving m1 <= f2_body under the assumption that m1 <= f2 args2
  {- FIXME: implement something like this
  Just (f2_body, True)
    | CompFunReturn <- k2 ->
      withFunAssumpR m1 f2 args2 $
   -}

    -- Otherwise we would have to somehow split m1 into some computation of the
    -- form m1' >>= k1 where m1' <= f2 args2 and k1 <= k2, but we don't know how
    -- to do this splitting, so give up
  _ ->
    throwError (CompsDoNotRefine m1 m2)


-- NOTE: the rules that introduce existential variables need to go last, so that
-- they can quantify over as many universals as possible
mrRefines' m1 (ExistsM tp f2) =
  do let nm = maybe "x" id (compFunVarName f2)
     evar <- mrFreshEVar nm tp
     m2' <- applyNormCompFun f2 evar
     mrRefines m1 m2'
mrRefines' (ForallM tp f1) m2 =
  do let nm = maybe "x" id (compFunVarName f1)
     evar <- mrFreshEVar nm tp
     m1' <- applyNormCompFun f1 evar
     mrRefines m1' m2

-- If none of the above cases match, then fail
mrRefines' m1 m2 = throwError (CompsDoNotRefine m1 m2)


-- | Prove that one function refines another for all inputs
mrRefinesFun :: CompFun -> CompFun -> MRM ()
mrRefinesFun CompFunReturn CompFunReturn = return ()
mrRefinesFun f1 f2
  | Just nm <- compFunVarName f1 `mplus` compFunVarName f2
  , Just tp <- compFunInputType f1 `mplus` compFunInputType f2 =
    withUVarLift nm tp (f1,f2) $ \x (f1', f2') ->
    do m1' <- applyNormCompFun f1' x
       m2' <- applyNormCompFun f2' x
       mrRefines m1' m2'
mrRefinesFun _ _ = error "mrRefinesFun: unreachable!"


----------------------------------------------------------------------
-- * External Entrypoints
----------------------------------------------------------------------

-- | Test two monadic, recursive terms for equivalence
askMRSolver ::
  SharedContext ->
  Int {- ^ The debug level -} ->
  SBV.SMTConfig {- ^ SBV configuration -} ->
  Maybe Integer {- ^ Timeout in milliseconds for each SMT call -} ->
  Term -> Term -> IO (Maybe MRFailure)

askMRSolver sc dlvl smt_conf timeout t1 t2 =
  do tp1 <- scTypeOf sc t1
     tp2 <- scTypeOf sc t2
     init_st <- mkMRState sc Map.empty smt_conf timeout dlvl
     case asPiList tp1 of
       (uvar_ctx, asCompM -> Just _) ->
         fmap (either Just (const Nothing)) $ runMRM init_st $
         withUVars uvar_ctx $ \vars ->
         do tps_are_eq <- mrConvertible tp1 tp2
            if tps_are_eq then return () else
              throwError (TypesNotEq (Type tp1) (Type tp2))
            mrDebugPPPrefixSep 1 "mr_solver" t1 "<=" t2
            m1 <- mrApplyAll t1 vars >>= normCompTerm
            m2 <- mrApplyAll t2 vars >>= normCompTerm
            mrRefines m1 m2
       _ -> return $ Just $ NotCompFunType tp1
