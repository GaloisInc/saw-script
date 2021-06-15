{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module SAWScript.Prover.MRSolver
  (askMRSolver, MRFailure(..), showMRFailure
  , SBV.SMTConfig
  , SBV.z3, SBV.cvc4, SBV.yices, SBV.mathSAT, SBV.boolector
  ) where

import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Semigroup

import Prettyprinter

import Verifier.SAW.Term.Functor
import Verifier.SAW.SharedTerm
import Verifier.SAW.Recognizer

import SAWScript.Proof (boolToProp)
import qualified SAWScript.Prover.SBV as SBV

import Prelude


newtype LocalFunName = LocalFunName { unLocalFunName :: ExtCns Term } deriving (Eq, Show)

-- | Names of functions to be used in computations, which are either local,
-- letrec-bound names (represented with an 'ExtCns'), or global named constants
data FunName = LocalName LocalFunName | GlobalName Ident
             deriving (Eq, Show)

funNameType :: FunName -> MRM Term
funNameType (LocalName (LocalFunName ec)) = return $ ecType ec
funNameType (GlobalName i) = liftSC1 scTypeOfGlobal i

-- | A "marking" consisting of a set of unfolded function names
newtype Mark = Mark [FunName] deriving (Semigroup, Monoid, Show)

inMark :: FunName -> Mark -> Bool
inMark f (Mark fs) = elem f fs

singleMark :: FunName -> Mark
singleMark f = Mark [f]

-- | A term specifically known to be of type @sort i@ for some @i@
newtype Type = Type Term deriving Show

-- | A computation in WHNF
data WHNFComp
  = Return Term -- ^ Terminates with a return
  | Error -- ^ Raises an error
  | If Term Comp Comp -- ^ If-then-else that returns @CompM a@
  | FunBind FunName [Term] Mark CompFun
    -- ^ Bind a monadic function with @N@ arguments in an @a -> CompM b@ term,
    -- marked with a set of function names
  deriving Show

-- | A computation function of type @a -> CompM b@ for some @a@ and @b@
data CompFun
  = CompFunTerm Term
  | CompFunComp CompFun CompFun
    -- ^ The monadic composition @f >=> g@
  | CompFunMark CompFun Mark
    -- ^ A computation marked with function names
  deriving Show

-- | A computation of type @CompM a@ for some @a@
data Comp = CompTerm Term | CompBind Comp CompFun | CompMark Comp Mark
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
  | MalformedInOutTypes Term
  | MalformedDefsFun Term
  | MalformedComp Term
  | NotCompFunType Term
  | MRFailureCtx FailCtx MRFailure
    -- ^ Records terms we were trying to compare when we got a failure
  | MRFailureDisj MRFailure MRFailure
    -- ^ Records a disjunctive branch we took, where both cases failed
  deriving Show

prettyTerm :: Term -> Doc ann
prettyTerm = unAnnotate . ppTerm defaultPPOpts

prettyAppList :: [Doc ann] -> Doc ann
prettyAppList = group . hang 2 . vsep

instance Pretty Type where
  pretty (Type t) = prettyTerm t

instance Pretty FunName where
  pretty (LocalName (LocalFunName ec)) = unAnnotate $ ppName $ ecName ec
  pretty (GlobalName i) = viaShow i

instance Pretty Comp where
  pretty (CompTerm t) = prettyTerm t
  pretty (CompBind c f) =
    prettyAppList [pretty c, ">>=", pretty f]
  pretty (CompMark c _) =
    -- FIXME: print the mark?
    pretty c

instance Pretty CompFun where
  pretty (CompFunTerm t) = prettyTerm t
  pretty (CompFunComp f g) =
    prettyAppList [pretty f, ">=>", pretty g]
  pretty (CompFunMark f _) =
    -- FIXME: print the mark?
    pretty f

instance Pretty WHNFComp where
  pretty (Return t) =
    prettyAppList ["returnM", parens (prettyTerm t)]
  pretty Error = "errorM"
  pretty (If cond t1 t2) =
    prettyAppList ["ite", prettyTerm cond,
                   parens (pretty t1), parens (pretty t2)]
  pretty (FunBind f [] _ k) =
    prettyAppList [pretty f, ">>=", pretty k]
  pretty (FunBind f args _ k) =
    prettyAppList
    [parens (prettyAppList (pretty f : map prettyTerm args)),
     ">>=" <+> pretty k]

vsepIndent24 :: Doc ann -> Doc ann -> Doc ann -> Doc ann -> Doc ann
vsepIndent24 d1 d2 d3 d4 =
  group (d1 <> nest 2 (line <> d2) <> line <> d3 <> nest 2 (line <> d4))

instance Pretty MRTerm where
  pretty (MRTermTerm t) = prettyTerm t
  pretty (MRTermType tp) = pretty tp
  pretty (MRTermComp comp) = pretty comp
  pretty (MRTermCompFun f) = pretty f
  pretty (MRTermWHNFComp norm) = pretty norm
  pretty (MRTermFunName nm) = "function" <+> pretty nm

instance Pretty FailCtx where
  pretty (FailCtxCmp t1 t2) =
    group $ nest 2 $ vsep ["When comparing terms:", pretty t1, pretty t2]
  pretty (FailCtxWHNF t) =
    group $ nest 2 $ vsep ["When normalizing computation:", prettyTerm t]

instance Pretty MRFailure where
  pretty (TermsNotEq t1 t2) =
    vsepIndent24
    "Terms not equal:" (prettyTerm t1)
    "and" (prettyTerm t2)
  pretty (TypesNotEq tp1 tp2) =
    vsepIndent24
    "Types not equal:" (pretty tp1)
    "and" (pretty tp2)
  pretty (ReturnNotError t) =
    nest 2 ("errorM not equal to" <+>
            group (hang 2 $ vsep ["returnM", prettyTerm t]))
  pretty (FunsNotEq nm1 nm2) =
    vsep ["Named functions not equal:", pretty nm1, pretty nm2]
  pretty (CannotLookupFunDef nm) =
    vsep ["Could not find definition for function:", pretty nm]
  pretty (RecursiveUnfold nm) =
    vsep ["Recursive unfolding of function inside its own body:",
          pretty nm]
  pretty (MalformedInOutTypes t) =
    "Not a ground InputOutputTypes list:"
    <> nest 2 (line <> prettyTerm t)
  pretty (MalformedDefsFun t) =
    "Cannot handle letRecM recursive definitions term:"
    <> nest 2 (line <> prettyTerm t)
  pretty (MalformedComp t) =
    "Could not handle computation:"
    <> nest 2 (line <> prettyTerm t)
  pretty (NotCompFunType tp) =
    "Not a computation or computational function type:"
    <> nest 2 (line <> prettyTerm tp)
  pretty (MRFailureCtx ctx err) =
    pretty ctx <> line <> pretty err
  pretty (MRFailureDisj err1 err2) =
    vsepIndent24 "Tried two comparisons:" (pretty err1)
    "Backtracking..." (pretty err2)

showMRFailure :: MRFailure -> String
showMRFailure = show . pretty

-- | State maintained by MR. Solver
data MRState = MRState {
  mrSC :: SharedContext,
  -- ^ Global shared context for building terms, etc.
  mrSMTConfig :: SBV.SMTConfig,
  -- ^ Global SMT configuration for the duration of the MR. Solver call
  mrSMTTimeout :: Maybe Integer,
  -- ^ SMT timeout for SMT calls made by Mr. Solver
  mrLocalFuns :: [(LocalFunName, Term)],
  -- ^ Letrec-bound function names with their definitions as lambda-terms
  mrFunEqs :: [((FunName, FunName), Bool)],
  -- ^ Cache of which named functions are equal
  mrPathCondition :: Term
  -- ^ The conjunction of all Boolean if conditions along the current path
}

-- | Monad used by the MR. Solver
type MRM = ExceptT MRFailure (StateT MRState IO)

-- | Run an 'MRM' computation, and apply a function to any failure thrown
mapFailure :: (MRFailure -> MRFailure) -> MRM a -> MRM a
mapFailure f m = catchError m (throwError . f)

-- | Try two different 'MRM' computations, combining their failures if needed
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

-- | Test if a Boolean term is "provable", i.e., its negation is unsatisfiable
mrProvable :: Term -> MRM Bool
mrProvable bool_prop =
  do smt_conf <- mrSMTConfig <$> get
     timeout <- mrSMTTimeout <$> get
     path_prop <- mrPathCondition <$> get
     bool_prop' <- liftSC2 scImplies path_prop bool_prop
     sc <- mrSC <$> get
     prop <- liftIO (boolToProp sc [] bool_prop')
     (smt_res, _) <- liftSC1 (SBV.proveUnintSBV smt_conf mempty timeout) prop
     case smt_res of
       Just _ -> return False
       Nothing -> return True

-- | Test if a Boolean term is satisfiable
mrSatisfiable :: Term -> MRM Bool
mrSatisfiable prop = not <$> (liftSC1 scNot prop >>= mrProvable)

-- | Test if two terms are equal using an SMT solver
mrTermsEq :: Term -> Term -> MRM Bool
mrTermsEq t1 t2 =
  do tp <- liftSC1 scTypeOf t1
     eq_fun_tm <- liftSC1 scGlobalDef "Prelude.eq"
     prop <- liftSC2 scApplyAll eq_fun_tm [tp, t1, t2]
     -- Remember, t1 == t2 is true iff t1 /= t2 is not satisfiable
     -- not_prop <- liftSC1 scNot prop
     -- not <$> mrSatisfiable not_prop
     mrProvable prop

-- | Run an equality-testing computation under the assumption of an additional
-- path condition. If the condition is unsatisfiable, the test is vacuously
-- true, so need not be run.
withPathCondition :: Term -> MRM () -> MRM ()
withPathCondition cond m =
  do sat <- mrSatisfiable cond
     if sat then
       do old_cond <- mrPathCondition <$> get
          new_cond <- liftSC2 scAnd old_cond cond
          modify $ \st -> st { mrPathCondition = new_cond }
          m
          modify $ \st -> st { mrPathCondition = old_cond }
       else return ()

-- | Like 'withPathCondition' but for the negation of a condition
withNotPathCondition :: Term -> MRM () -> MRM ()
withNotPathCondition cond m =
  liftSC1 scNot cond >>= \cond' -> withPathCondition cond' m

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
  (LocalName <$> LocalFunName <$> asExtCns t)
  `mplus` (GlobalName <$> asGlobalDef t)

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

-- | Take in an @InputOutputTypes@ list (as a SAW core term) and build a fresh
-- function variable for each pair of input and output types in it
mkFunVarsForTps :: Term -> MRM [LocalFunName]
mkFunVarsForTps (asCtor -> Just (primName -> "Prelude.TypesNil", [])) =
  return []
mkFunVarsForTps (asCtor -> Just (primName -> "Prelude.TypesCons", [a, b, tps])) =
  do compM <- liftSC1 scGlobalDef "Prelude.CompM"
     comp_b <- liftSC2 scApply compM b
     tp <- liftSC3 scPi "x" a comp_b
     rest <- mkFunVarsForTps tps
     ec <- liftSC2 scFreshEC "f" tp
     return (LocalFunName ec : rest)
mkFunVarsForTps t = throwError (MalformedInOutTypes t)

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
         do funs <- mkFunVarsForTps tps
            fun_tms <- mapM (liftSC1 scFlatTermF . ExtCns . unLocalFunName) funs
            funs_tm <-
              foldr ((=<<) . liftSC2 scPairValue) (liftSC0 scUnitValue) fun_tms
            defs_tm <- liftSC2 scApply defs_f funs_tm >>= liftSC1 scWhnf
            defs <- case asTupleValue defs_tm of
              Just defs -> return defs
              Nothing -> throwError (MalformedDefsFun defs_f)
            modify $ \st ->
              st { mrLocalFuns = (zip funs defs) ++ mrLocalFuns st }
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
mrLookupFunDef f@(LocalName nm) =
  do fun_assoc <- mrLocalFuns <$> get
     case lookup nm fun_assoc of
       Just body -> return body
       Nothing -> throwError (CannotLookupFunDef f)

-- | Unfold a call to function @f@ in term @f args >>= g@
mrUnfoldFunBind :: FunName -> [Term] -> Mark -> CompFun -> MRM Comp
mrUnfoldFunBind f _ mark _ | inMark f mark = throwError (RecursiveUnfold f)
mrUnfoldFunBind f args mark g =
  do f_def <- mrLookupFunDef f
     CompBind <$>
       (CompMark <$> (CompTerm <$> liftSC2 scApplyAll f_def args)
        <*> (return $ singleMark f `mappend` mark))
       <*> return g

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
        do tp1 <- funNameType f1
           tp2 <- funNameType f2
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
