{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.JVM.CrucibleOverride
  ( OverrideMatcher(..)
  , runOverrideMatcher

  , setupValueSub
  , osAsserts
  , termSub

  , learnCond
  , matchArg
  , methodSpecHandler
  , valueToSC
  , termId
  , injectJVMVal
  , doAllocateObject
  , doAllocateArray
  , doFieldStore
  , doArrayStore
  , decodeJVMVal
  , unassignedJVMValue
  ) where

import           Control.Lens
import           Control.Exception as X
import           Control.Monad.ST (RealWorld, stToIO)
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class
import           Control.Monad.IO.Class
import           Control.Monad
import           Data.Either (partitionEithers)
import           Data.Foldable (for_, traverse_)
import           Data.List (tails)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Vector as V
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- cryptol
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)
import qualified Cryptol.Utils.PP as Cryptol

-- what4
import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4
import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible ( TypeRepr(UnitRepr) )
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator, freshRefCell)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.EvalStmt as EvalStmt (readRef, alterRef)
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Types as Crucible
import qualified Lang.Crucible.Utils.MuxTree as Crucible (toMuxTree)

-- crucible-saw
import qualified Lang.Crucible.Backend.SAWCore as CrucibleSAW

-- crucible-jvm
import qualified Lang.Crucible.JVM.Translation as CJ

-- parameterized-utils
import           Data.Parameterized.Classes ((:~:)(..), testEquality, knownRepr, ixF)
import qualified Data.Parameterized.Context as Ctx
-- import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.TraversableFC as Ctx

-- saw-core
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Prelude (scEq)
import           Verifier.SAW.TypedAST
import           Verifier.SAW.Recognizer
import           Verifier.SAW.TypedTerm

--import           SAWScript.JavaExpr (JavaType(..))
import           SAWScript.JVM.CrucibleMethodSpecIR
import           SAWScript.JVM.CrucibleResolveSetupValue
import           SAWScript.Options
import           SAWScript.Utils (handleException)

-- jvm-parser
import qualified Language.JVM.Parser as J

-- | The 'OverrideMatcher' type provides the operations that are needed
-- to match a specification's arguments with the arguments provided by
-- the Crucible simulation in order to compute the variable substitution
-- and side-conditions needed to proceed.
newtype OverrideMatcher a =
  OM (StateT OverrideState (ExceptT OverrideFailure IO) a)
  deriving (Functor, Applicative, Monad, MonadIO)

data OverrideState = OverrideState
  { -- | Substitution for memory allocations
    _setupValueSub :: Map AllocIndex JVMRefVal

    -- | Substitution for SAW Core external constants
  , _termSub :: Map VarIndex Term

    -- | Free variables available for unification
  , _osFree :: Set VarIndex

    -- | Accumulated assertions
  , _osAsserts :: [(W4.Pred Sym, Crucible.SimError)]

    -- | Accumulated assumptions
  , _osAssumes :: [W4.Pred Sym]

    -- | Symbolic simulation state
  , _syminterface :: Sym

    -- | Global variables
  , _overrideGlobals :: Crucible.SymGlobalState Sym

    -- | Source location to associated with this override
  , _osLocation :: W4.ProgramLoc
  }

data OverrideFailureReason
  = AmbiguousPointsTos [PointsTo]
  | AmbiguousVars [TypedTerm]
  | BadTermMatch Term Term -- ^ simulated and specified terms did not match
  | BadPointerCast -- ^ Pointer required to process points-to
  | BadReturnSpecification -- ^ type mismatch in return specification
  | NonlinearPatternNotSupported
  | BadPointerLoad String -- ^ loadRaw failed due to type error
  | StructuralMismatch JVMVal
                       SetupValue
                       J.Type
                        -- ^ simulated value, specified value, specified type

ppOverrideFailureReason :: OverrideFailureReason -> PP.Doc
ppOverrideFailureReason rsn = case rsn of
  AmbiguousPointsTos pts ->
    PP.text "ambiguous collection of points-to assertions" PP.<$$>
    (PP.indent 2 $ PP.vcat (map ppPointsTo pts))
  AmbiguousVars vs ->
    PP.text "ambiguous collection of variables" PP.<$$>
    (PP.indent 2 $ PP.vcat (map ppTypedTerm vs))
  BadTermMatch x y ->
    PP.text "terms do not match" PP.<$$>
    (PP.indent 2 (ppTerm defaultPPOpts x)) PP.<$$>
    (PP.indent 2 (ppTerm defaultPPOpts y))
  BadPointerCast ->
    PP.text "bad pointer cast"
  BadReturnSpecification ->
    PP.text "bad return specification"
  NonlinearPatternNotSupported ->
    PP.text "nonlinear pattern no supported"
  BadPointerLoad msg ->
    PP.text "type error when loading through pointer" PP.<$$>
    PP.indent 2 (PP.text msg)
  StructuralMismatch llvmval setupval ty ->
    PP.text "could not match the following terms" PP.<$$>
    PP.indent 2 (PP.text $ show llvmval) PP.<$$>
    PP.indent 2 (ppSetupValue setupval) PP.<$$>
    PP.text "with type" PP.<$$>
    PP.indent 2 (PP.text (show ty))

ppTypedTerm :: TypedTerm -> PP.Doc
ppTypedTerm (TypedTerm tp tm) =
  ppTerm defaultPPOpts tm
  PP.<+> PP.text ":" PP.<+>
  PP.text (show (Cryptol.ppPrec 0 tp))

ppPointsTo :: PointsTo -> PP.Doc
ppPointsTo pt =
  case pt of
    PointsToField _loc ptr fname val ->
      ppSetupValue ptr PP.<> "." PP.<> PP.text fname PP.<+> PP.text "|->" PP.<+> ppSetupValue val
    PointsToElem _loc ptr idx val ->
      ppSetupValue ptr PP.<> PP.brackets (PP.text (show idx)) PP.<+> PP.text "|->" PP.<+> ppSetupValue val

ppSetupValue :: SetupValue -> PP.Doc
ppSetupValue setupval = case setupval of
  SetupTerm tm   -> ppTypedTerm tm
  SetupVar i     -> PP.text ("@" ++ show i)
  SetupNull      -> PP.text "null"
  SetupGlobal nm -> PP.text ("global(" ++ nm ++ ")")

instance PP.Pretty OverrideFailureReason where
  pretty = ppOverrideFailureReason

instance Show OverrideFailureReason where
  show = show . PP.pretty

data OverrideFailure = OF W4.ProgramLoc OverrideFailureReason

ppOverrideFailure :: OverrideFailure -> PP.Doc
ppOverrideFailure (OF loc rsn) =
  PP.text "at" PP.<+> PP.pretty (W4.plSourceLoc loc) PP.<$$>
  ppOverrideFailureReason rsn

instance PP.Pretty OverrideFailure where
  pretty = ppOverrideFailure

instance Show OverrideFailure where
  show = show . PP.pretty

instance Exception OverrideFailure

makeLenses ''OverrideState

------------------------------------------------------------------------

-- | The initial override matching state starts with an empty substitution
-- and no assertions or assumptions.
initialState ::
  Sym                           {- ^ simulator                       -} ->
  Crucible.SymGlobalState Sym   {- ^ initial global variables        -} ->
  Map AllocIndex JVMRefVal      {- ^ initial allocation substitution -} ->
  Map VarIndex Term             {- ^ initial term substitution       -} ->
  Set VarIndex                  {- ^ initial free terms              -} ->
  W4.ProgramLoc                 {- ^ location information for the override -} ->
  OverrideState
initialState sym globals allocs terms free loc =
  OverrideState
  { _osAsserts       = []
  , _osAssumes       = []
  , _syminterface    = sym
  , _overrideGlobals = globals
  , _termSub         = terms
  , _osFree          = free
  , _setupValueSub   = allocs
  , _osLocation      = loc
  }

------------------------------------------------------------------------

addAssert ::
  W4.Pred Sym       {- ^ property -} ->
  Crucible.SimError {- ^ reason   -} ->
  OverrideMatcher ()
addAssert p r = OM (osAsserts %= cons (p,r))

addAssume ::
  W4.Pred Sym       {- ^ property -} ->
  OverrideMatcher ()
addAssume p = OM (osAssumes %= cons p)

readGlobal ::
  Crucible.GlobalVar tp ->
  OverrideMatcher (Crucible.RegValue Sym tp)
readGlobal k =
  do mb <- OM (uses overrideGlobals (Crucible.lookupGlobal k))
     case mb of
       Nothing -> fail ("No such global: " ++ show k)
       Just v  -> return v

writeGlobal ::
  Crucible.GlobalVar    tp ->
  Crucible.RegValue Sym tp ->
  OverrideMatcher ()
writeGlobal k v = OM (overrideGlobals %= Crucible.insertGlobal k v)

------------------------------------------------------------------------

-- | Abort the current computation by raising the given 'OverrideFailure'
-- exception.
failure :: W4.ProgramLoc -> OverrideFailureReason -> OverrideMatcher a
failure loc e = OM (lift (throwE (OF loc e)))

------------------------------------------------------------------------

-- | This function is responsible for implementing the \"override\" behavior
--   of method specifications.  The main work done in this function to manage
--   the process of selecting between several possible different override
--   specifications that could apply.  We want a proof to succeed if /any/
--   choice of method spec allows the proof to go through, which is a slightly
--   awkward thing to fit into the symbolic simulation framework.
--
--   The main work of determining the preconditions, postconditions, memory
--   updates and return value for a single specification is done by
--   the @methodSpecHandler_prestate@ and @methodSpecHandler_poststate@ functions.
--
--   In a first phase, we attempt to apply the precondition portion of each of
--   the given method specifications.  Each of them that might apply generate
--   a substitution for the setup variables and a collection of preconditions
--   that guard the specification.  We use these preconditions to compute
--   a multiway symbolic branch, one for each override which might apply.
--
--   In the body of each of the individual branches, we compute the postcondition
--   actions of the corresponding method specification.  This will update memory
--   and compute function return values, in addition to assuming postcondition
--   predicates.
methodSpecHandler ::
  forall rtp args ret.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext          {- ^ context for interacting with Crucible        -} ->
  W4.ProgramLoc            {- ^ Location of the call site for error reporting-} ->
  [CrucibleMethodSpecIR]   {- ^ specification for current function override  -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  Crucible.OverrideSim (CrucibleSAW.SAWCruciblePersonality Sym) Sym CJ.JVM rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc top_loc css retTy = do
  sym <- Crucible.getSymInterface
  Crucible.RegMap args <- Crucible.getOverrideArgs

  -- First, run the precondition matcher phase.  Collect together a list of the results.
  -- For each override, this will either be an error message, or a matcher state and
  -- a method spec.
  prestates <-
    do g0 <- Crucible.readGlobals
       forM css $ \cs -> liftIO $
         let initialFree = Set.fromList (map (termId . ttTerm)
                                           (view (csPreState.csFreshVars) cs))
          in runOverrideMatcher sym g0 Map.empty Map.empty initialFree (view csLoc cs)
                      (do methodSpecHandler_prestate opts sc cc args cs
                          return cs)

  -- Print a failure message if all overrides failed to match.  Otherwise, collect
  -- all the override states that might apply, and compute the conjunction of all
  -- the preconditions.  We'll use these to perform symbolic branches between the
  -- various overrides.
  branches <- case partitionEithers prestates of
                (e, []) ->
                  fail $ show $
                    PP.text "All overrides failed during structural matching:" PP.<$$>
                    PP.vcat (map (\x -> PP.text "*" PP.<> PP.indent 2 (ppOverrideFailure x)) e)
                (_, ss) -> liftIO $
                  forM ss $ \(cs,st) ->
                    do precond <- W4.andAllOf sym (folded._1) (st^.osAsserts)
                       return ( precond, cs, st )

  -- Now use crucible's symbolic branching machinery to select between the branches.
  -- Essentially, we are doing an n-way if statement on the precondition predicates
  -- for each override, and selecting the first one whose preconditions hold.
  --
  -- Then, in the body of the branch, we run the poststate handler to update the
  -- memory state, compute return values and compute postcondition predicates.
  --
  -- For each override branch that doesn't fail outright, we assume the relevant
  -- postconditions, update the crucible global variable state, and return the
  -- computed return value.
  --
  -- We add a final default branch that simply fails unless some previous override
  -- branch has already succeeded.
  Crucible.regValue <$> Crucible.callOverride
     (Crucible.mkOverride' "overrideBranches" retTy
       (Crucible.symbolicBranches Crucible.emptyRegMap $
         [ ( precond
           , do g <- Crucible.readGlobals
                res <- liftIO $ runOverrideMatcher sym g
                   (st^.setupValueSub)
                   (st^.termSub)
                   (st^.osFree)
                   (st^.osLocation)
                   (methodSpecHandler_poststate opts sc cc retTy cs)
                case res of
                  Left (OF loc rsn)  ->
                    -- TODO, better pretty printing for reasons
                    liftIO $ Crucible.abortExecBecause
                      (Crucible.AssumedFalse (Crucible.AssumptionReason loc (show rsn)))
                  Right (ret,st') ->
                    do liftIO $ forM_ (st'^.osAssumes) $ \asum ->
                         Crucible.addAssumption (cc^.ccBackend)
                            (Crucible.LabeledPred asum
                              (Crucible.AssumptionReason (st^.osLocation) "override postcondition"))
                       Crucible.writeGlobals (st'^.overrideGlobals)
                       Crucible.overrideReturn' (Crucible.RegEntry retTy ret)
           , Just (W4.plSourceLoc (cs^.csLoc))
           )
         | (precond, cs, st) <- branches
         ] ++
        [

            let fnName = case branches of
                           (_, cs, _) : _  -> cs^.csMethodName
                           _               -> "unknown function"
            in
            ( W4.truePred sym
            , liftIO $ Crucible.addFailedAssertion sym (Crucible.GenericSimError $ "no override specification applies for " ++ fnName)
            , Just (W4.plSourceLoc top_loc)
            )
        ]
       ))
     (Crucible.RegMap args)

------------------------------------------------------------------------

-- | Use a method spec to override the behavior of a function.
--   This function computes the pre-state portion of the override,
--   which involves reading values from arguments and memory and computing
--   substitutions for the setup value variables, and computing precondition
--   predicates.
methodSpecHandler_prestate ::
  forall ctx.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext          {- ^ context for interacting with Crucible        -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
                           {- ^ the arguments to the function -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher ()
methodSpecHandler_prestate opts sc cc args cs =
  do let expectedArgTypes = {-(traverse . _1) resolveMemType-} (Map.elems (cs^.csArgBindings))
     let aux ::
           (J.Type, SetupValue) -> Crucible.AnyValue Sym ->
           IO (JVMVal, J.Type, SetupValue)
         aux (argTy, setupVal) val =
           case decodeJVMVal argTy val of
             Just val' -> return (val', argTy, setupVal)
             Nothing -> fail "unexpected type"

     -- todo: fail if list lengths mismatch
     xs <- liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

     sequence_ [ matchArg sc cc (cs^.csLoc) PreState x y z | (x, y, z) <- xs]

     learnCond opts sc cc cs PreState (cs^.csPreState)


-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall ret.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext          {- ^ context for interacting with Crucible        -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher (Crucible.RegValue Sym ret)
methodSpecHandler_poststate opts sc cc retTy cs =
  do executeCond opts sc cc cs (cs^.csPostState)
     computeReturnValue opts cc sc cs retTy (cs^.csRetValue)

-- learn pre/post condition
learnCond ::
  Options ->
  SharedContext ->
  CrucibleContext ->
  CrucibleMethodSpecIR ->
  PrePost ->
  StateSpec ->
  OverrideMatcher ()
learnCond opts sc cc cs prepost ss =
  do let loc = cs^.csLoc
     matchPointsTos opts sc cc cs prepost (ss^.csPointsTos)
     traverse_ (learnSetupCondition opts sc cc cs prepost) (ss^.csConditions)
     enforceDisjointness cc loc ss
     enforceCompleteSubstitution loc ss


-- | Verify that all of the fresh variables for the given
-- state spec have been "learned". If not, throws
-- 'AmbiguousVars' exception.
enforceCompleteSubstitution :: W4.ProgramLoc -> StateSpec -> OverrideMatcher ()
enforceCompleteSubstitution loc ss =

  do sub <- OM (use termSub)

     let -- predicate matches terms that are not covered by the computed
         -- term substitution
         isMissing tt = termId (ttTerm tt) `Map.notMember` sub

         -- list of all terms not covered by substitution
         missing = filter isMissing (view csFreshVars ss)

     unless (null missing) (failure loc (AmbiguousVars missing))


-- | Given a 'Term' that must be an external constant, extract the 'VarIndex'.
termId :: Term -> VarIndex
termId t =
  case asExtCns t of
    Just ec -> ecVarIndex ec
    _       -> error "termId expected a variable"


-- execute a pre/post condition
executeCond ::
  Options ->
  SharedContext ->
  CrucibleContext ->
  CrucibleMethodSpecIR ->
  StateSpec ->
  OverrideMatcher ()
executeCond opts sc cc cs ss =
  do refreshTerms sc ss
     traverse_ (executeAllocation opts cc) (Map.assocs (ss^.csAllocs))
     traverse_ (executePointsTo opts sc cc cs) (ss^.csPointsTos)
     traverse_ (executeSetupCondition opts sc cc cs) (ss^.csConditions)


-- | Allocate fresh variables for all of the "fresh" vars
-- used in this phase and add them to the term substitution.
refreshTerms ::
  SharedContext {- ^ shared context -} ->
  StateSpec     {- ^ current phase spec -} ->
  OverrideMatcher ()
refreshTerms sc ss =
  do extension <- Map.fromList <$> traverse freshenTerm (view csFreshVars ss)
     OM (termSub %= Map.union extension)
  where
    freshenTerm tt =
      case asExtCns (ttTerm tt) of
        Just ec -> do new <- liftIO (mkTypedTerm sc =<< scFreshGlobal sc (ecName ec) (ecType ec))
                      return (termId (ttTerm tt), ttTerm new)
        Nothing -> error "refreshTerms: not a variable"

------------------------------------------------------------------------

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint.
enforceDisjointness ::
  CrucibleContext -> W4.ProgramLoc -> StateSpec -> OverrideMatcher ()
enforceDisjointness _cc loc ss =
  do sym <- getSymInterface
     sub <- OM (use setupValueSub)
     let mems = Map.elems $ Map.intersectionWith (,) (view csAllocs ss) sub

     -- Ensure that all regions are disjoint from each other.
     sequence_
        [ do c <- liftIO $ W4.notPred sym =<< refIsEqual sym p q
             addAssert c a

        | let a = Crucible.SimError loc $
                    Crucible.AssertFailureSimError "Memory regions not disjoint"
        , ((_ploc, _pty), p) : ps <- tails mems
        , ((_qloc, _qty), q)      <- ps
        ]

------------------------------------------------------------------------

-- | For each points-to statement read the memory value through the
-- given pointer (lhs) and match the value against the given pattern
-- (rhs).  Statements are processed in dependency order: a points-to
-- statement cannot be executed until bindings for any/all lhs
-- variables exist.
matchPointsTos ::
  Options          {- ^ saw script print out opts -} ->
  SharedContext    {- ^ term construction context -} ->
  CrucibleContext  {- ^ simulator context     -}     ->
  CrucibleMethodSpecIR                               ->
  PrePost                                            ->
  [PointsTo]       {- ^ points-tos                -} ->
  OverrideMatcher ()
matchPointsTos opts sc cc spec prepost = go False []
  where
    go ::
      Bool       {- progress indicator -} ->
      [PointsTo] {- delayed conditions -} ->
      [PointsTo] {- queued conditions  -} ->
      OverrideMatcher ()

    -- all conditions processed, success
    go _ [] [] = return ()

    -- not all conditions processed, no progress, failure
    go False delayed [] = failure (spec^.csLoc) (AmbiguousPointsTos delayed)

    -- not all conditions processed, progress made, resume delayed conditions
    go True delayed [] = go False [] delayed

    -- progress the next points-to in the work queue
    go progress delayed (c:cs) =
      do ready <- checkPointsTo c
         if ready then
           do learnPointsTo opts sc cc spec prepost c
              go True delayed cs
         else
           do go progress (c:delayed) cs

    -- determine if a precondition is ready to be checked
    checkPointsTo :: PointsTo -> OverrideMatcher Bool
    checkPointsTo (PointsToField _loc p _ _) = checkSetupValue p
    checkPointsTo (PointsToElem _loc p _ _) = checkSetupValue p

    checkSetupValue :: SetupValue -> OverrideMatcher Bool
    checkSetupValue v =
      do m <- OM (use setupValueSub)
         return (all (`Map.member` m) (setupVars v))

    -- Compute the set of variable identifiers in a 'SetupValue'
    setupVars :: SetupValue -> Set AllocIndex
    setupVars v =
      case v of
        SetupVar    i  -> Set.singleton i
        --SetupStruct xs -> foldMap setupVars xs
        --SetupArray  xs -> foldMap setupVars xs
        --SetupElem x _  -> setupVars x
        --SetupField x _ -> setupVars x
        SetupTerm   _  -> Set.empty
        SetupNull      -> Set.empty
        SetupGlobal _  -> Set.empty


------------------------------------------------------------------------

computeReturnValue ::
  Options               {- ^ saw script debug and print options     -} ->
  CrucibleContext       {- ^ context of the crucible simulation     -} ->
  SharedContext         {- ^ context for generating saw terms       -} ->
  CrucibleMethodSpecIR  {- ^ method specification                   -} ->
  Crucible.TypeRepr ret {- ^ representation of function return type -} ->
  Maybe SetupValue      {- ^ optional symbolic return value         -} ->
  OverrideMatcher (Crucible.RegValue Sym ret)
                        {- ^ concrete return value                  -}

computeReturnValue _opts _cc _sc spec ty Nothing =
  case ty of
    Crucible.UnitRepr -> return ()
    _ -> failure (spec^.csLoc) BadReturnSpecification

computeReturnValue opts cc sc spec ty (Just val) =
  do (_memTy, val') <- resolveSetupValueJVM opts cc sc spec val
     case val' of
       IVal i ->
         case testEquality ty CJ.intRepr of
           Just Refl -> return i
           Nothing -> failure (spec^.csLoc) BadReturnSpecification
       LVal l ->
         case testEquality ty CJ.longRepr of
           Just Refl -> return l
           Nothing -> failure (spec^.csLoc) BadReturnSpecification
       RVal r ->
         case testEquality ty CJ.refRepr of
           Just Refl -> return r
           Nothing -> failure (spec^.csLoc) BadReturnSpecification


------------------------------------------------------------------------

-- | Forget the type indexes and length of the arguments.
assignmentToList ::
  Ctx.Assignment (Crucible.RegEntry sym) ctx ->
  [Crucible.AnyValue sym]
assignmentToList = Ctx.toListFC (\(Crucible.RegEntry x y) -> Crucible.AnyValue x y)

------------------------------------------------------------------------

getSymInterface :: OverrideMatcher Sym
getSymInterface = OM (use syminterface)

------------------------------------------------------------------------

-- | "Run" function for OverrideMatcher. The final result and state
-- are returned. The state will contain the updated globals and substitutions
runOverrideMatcher ::
  Sym                         {- ^ simulator                       -} ->
  Crucible.SymGlobalState Sym {- ^ initial global variables        -} ->
  Map AllocIndex JVMRefVal    {- ^ initial allocation substitution -} ->
  Map VarIndex Term           {- ^ initial term substitution       -} ->
  Set VarIndex                {- ^ initial free variables          -} ->
  W4.ProgramLoc               {- ^ override location information   -} ->
  OverrideMatcher a           {- ^ matching action                 -} ->
  IO (Either OverrideFailure (a, OverrideState))
runOverrideMatcher sym g a t free loc (OM m) = runExceptT (runStateT m (initialState sym g a t free loc))

------------------------------------------------------------------------

-- | Assign the given pointer value to the given allocation index in
-- the current substitution. If there is already a binding for this
-- index, then add a pointer-equality constraint.
assignVar ::
  CrucibleContext {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  AllocIndex {- ^ variable index -} ->
  JVMRefVal  {- ^ concrete value -} ->
  OverrideMatcher ()

assignVar cc loc var ref =
  do old <- OM (setupValueSub . at var <<.= Just ref)
     let sym = cc^.ccBackend
     for_ old $ \ref' ->
       do p <- liftIO (refIsEqual sym ref ref')
          addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError "equality of aliased pointers"))

------------------------------------------------------------------------


assignTerm ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  CrucibleContext    {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                          ->
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher ()

assignTerm sc cc loc prepost var val =
  do mb <- OM (use (termSub . at var))
     case mb of
       Nothing -> OM (termSub . at var ?= val)
       Just old ->
         matchTerm sc cc loc prepost val old


------------------------------------------------------------------------

-- | Match the value of a function argument with a symbolic 'SetupValue'.
matchArg ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  CrucibleContext    {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                          ->
  JVMVal             {- ^ concrete simulation value             -} ->
  J.Type             {- ^ expected memory type                  -} ->
  SetupValue         {- ^ expected specification value          -} ->
  OverrideMatcher ()

matchArg sc cc loc prepost actual expectedTy expected@(SetupTerm expectedTT)
  | Cryptol.Forall [] [] tyexpr <- ttSchema expectedTT
  , Right tval <- Cryptol.evalType mempty tyexpr
  = do sym <- getSymInterface
       let failMsg = StructuralMismatch actual expected expectedTy
       realTerm <- valueToSC sym loc failMsg tval actual
       matchTerm sc cc loc prepost realTerm (ttTerm expectedTT)

matchArg _sc cc loc prepost actual@(RVal ref) expectedTy setupval =
  case setupval of
    SetupVar var ->
      do assignVar cc loc var ref

    SetupNull ->
      do sym <- getSymInterface
         p   <- liftIO (refIsNull sym ref)
         addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError ("null-equality " ++ stateCond prepost)))

    SetupGlobal name ->
      do let mem = () -- FIXME cc^.ccLLVMEmptyMem
         sym  <- getSymInterface
         ref' <- liftIO $ doResolveGlobal sym mem name

         p  <- liftIO (refIsEqual sym ref ref')
         addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError ("global-equality " ++ stateCond prepost)))

    _ -> failure loc (StructuralMismatch actual setupval expectedTy)

matchArg _sc _cc loc _prepost actual expectedTy expected =
  failure loc (StructuralMismatch actual expected expectedTy)

------------------------------------------------------------------------

valueToSC ::
  Sym ->
  W4.ProgramLoc ->
  OverrideFailureReason ->
  Cryptol.TValue ->
  JVMVal ->
  OverrideMatcher Term
valueToSC sym _ _ Cryptol.TVBit (IVal x) =
  do b <- liftIO $ W4.bvIsNonzero sym x
      -- TODO: assert that x is 0 or 1
     liftIO (CrucibleSAW.toSC sym b)

valueToSC sym _ _ (Cryptol.TVSeq _n Cryptol.TVBit) (IVal x) =
  liftIO (CrucibleSAW.toSC sym x)

valueToSC sym _ _ (Cryptol.TVSeq _n Cryptol.TVBit) (LVal x) =
  liftIO (CrucibleSAW.toSC sym x)

valueToSC _sym loc failMsg _tval _val =
  failure loc failMsg
-- TODO: check sizes on bitvectors, support bool, char, and short types

------------------------------------------------------------------------

matchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  CrucibleContext {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                       ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher ()

matchTerm _ _ _ _ real expect | real == expect = return ()
matchTerm sc cc loc prepost real expect =
  do free <- OM (use osFree)
     case unwrapTermF expect of
       FTermF (ExtCns ec)
         | Set.member (ecVarIndex ec) free ->
         do assignTerm sc cc loc prepost (ecVarIndex ec) real

       _ ->
         do t <- liftIO $ scEq sc real expect
            p <- liftIO $ resolveBoolTerm (cc^.ccBackend) t
            addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError ("literal equality " ++ stateCond prepost)))

------------------------------------------------------------------------

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
learnSetupCondition ::
  Options                    ->
  SharedContext              ->
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  PrePost                    ->
  SetupCondition             ->
  OverrideMatcher ()
learnSetupCondition opts sc cc spec prepost (SetupCond_Equal loc val1 val2)  = learnEqual opts sc cc spec loc prepost val1 val2
learnSetupCondition _opts sc cc _    prepost (SetupCond_Pred loc tm)         = learnPred sc cc loc prepost (ttTerm tm)

------------------------------------------------------------------------

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
learnPointsTo ::
  Options                    ->
  SharedContext              ->
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  PrePost                    ->
  PointsTo                   ->
  OverrideMatcher ()
learnPointsTo opts sc cc spec prepost pt =
  case pt of

    PointsToField loc ptr fname val ->
      do let tyenv = csAllocations spec
         let nameEnv = csTypeNames spec
         ty <- typeOfSetupValue cc tyenv nameEnv val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         sym <- getSymInterface
         globals <- OM (use overrideGlobals)
         v <- liftIO $ doFieldLoad sym loc globals ty rval fname
         matchArg sc cc loc prepost v ty val

    PointsToElem loc ptr idx val ->
      do let tyenv = csAllocations spec
         let nameEnv = csTypeNames spec
         ty <- typeOfSetupValue cc tyenv nameEnv val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         sym <- getSymInterface
         globals <- OM (use overrideGlobals)
         v <- liftIO $ doArrayLoad sym loc globals ty rval idx
         matchArg sc cc loc prepost v ty val


------------------------------------------------------------------------

stateCond :: PrePost -> String
stateCond PreState = "precondition"
stateCond PostState = "postcondition"

-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Options                                          ->
  SharedContext                                    ->
  CrucibleContext                                  ->
  CrucibleMethodSpecIR                             ->
  W4.ProgramLoc                                    ->
  PrePost                                          ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher ()
learnEqual opts sc cc spec loc prepost v1 v2 =
  do (_, val1) <- resolveSetupValueJVM opts cc sc spec v1
     (_, val2) <- resolveSetupValueJVM opts cc sc spec v2
     p         <- liftIO (equalValsPred cc val1 val2)
     let name = "equality " ++ stateCond prepost
     addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError name))

-- | Process a "crucible_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  CrucibleContext                                                     ->
  W4.ProgramLoc                                                       ->
  PrePost                                                             ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher ()
learnPred sc cc loc prepost t =
  do s <- OM (use termSub)
     u <- liftIO $ scInstantiateExt sc s t
     p <- liftIO $ resolveBoolTerm (cc^.ccBackend) u
     addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError (stateCond prepost)))

------------------------------------------------------------------------

-- TODO: replace (W4.ProgramLoc, J.Type) by some allocation datatype
-- that includes constructors for object allocations and array
-- allocations (with length).

-- | Perform an allocation as indicated by a 'crucible_alloc'
-- statement from the postcondition section.
executeAllocation ::
  Options                        ->
  CrucibleContext                ->
  (AllocIndex, (W4.ProgramLoc, Allocation)) ->
  OverrideMatcher ()
executeAllocation opts cc (var, (loc, alloc)) =
  do liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show alloc]
     let jc = cc^.ccJVMContext
     let halloc = cc^.ccHandleAllocator
     sym <- getSymInterface
     globals <- OM (use overrideGlobals)
     (ptr, globals') <-
       case alloc of
         AllocObject cname -> liftIO $ doAllocateObject sym halloc jc cname globals
         AllocArray len elemTy -> liftIO $ doAllocateArray sym halloc jc len elemTy globals
     OM (overrideGlobals .= globals')
     assignVar cc loc var ptr

------------------------------------------------------------------------

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  Options                    ->
  SharedContext              ->
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  SetupCondition             ->
  OverrideMatcher ()
executeSetupCondition opts sc cc spec (SetupCond_Equal _loc val1 val2) = executeEqual opts sc cc spec val1 val2
executeSetupCondition _opts sc cc _    (SetupCond_Pred _loc tm)        = executePred sc cc tm

------------------------------------------------------------------------

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  Options                    ->
  SharedContext              ->
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  PointsTo                   ->
  OverrideMatcher ()
executePointsTo opts sc cc spec pt =
  case pt of

    PointsToField loc ptr fname val ->
      do (_, val') <- resolveSetupValueJVM opts cc sc spec val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         sym <- getSymInterface
         globals <- OM (use overrideGlobals)
         globals' <- liftIO $ doFieldStore sym globals rval fname val'
         OM (overrideGlobals .= globals')

    PointsToElem loc ptr idx val ->
      do (_, val') <- resolveSetupValueJVM opts cc sc spec val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         sym <- getSymInterface
         globals <- OM (use overrideGlobals)
         globals' <- liftIO $ doArrayStore sym globals rval idx val'
         OM (overrideGlobals .= globals')

------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  Options                                          ->
  SharedContext                                    ->
  CrucibleContext                                  ->
  CrucibleMethodSpecIR                             ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher ()
executeEqual opts sc cc spec v1 v2 =
  do (_, val1) <- resolveSetupValueJVM opts cc sc spec v1
     (_, val2) <- resolveSetupValueJVM opts cc sc spec v2
     p         <- liftIO (equalValsPred cc val1 val2)
     addAssume p

-- | Process a "crucible_postcond" statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext   ->
  CrucibleContext ->
  TypedTerm        {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher ()
executePred sc cc tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveBoolTerm (cc^.ccBackend) t
     addAssume p

------------------------------------------------------------------------

-- | Map the given substitution over all 'SetupTerm' constructors in
-- the given 'SetupValue'.
instantiateSetupValue ::
  SharedContext     ->
  Map VarIndex Term ->
  SetupValue        ->
  IO SetupValue
instantiateSetupValue sc s v =
  case v of
    SetupVar _     -> return v
    SetupTerm tt   -> SetupTerm <$> doTerm tt
    SetupNull      -> return v
    SetupGlobal _  -> return v
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

------------------------------------------------------------------------

resolveSetupValueJVM ::
  Options              ->
  CrucibleContext      ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher (J.Type, JVMVal)
resolveSetupValueJVM opts cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = csAllocations spec
         nameEnv = csTypeNames spec
     memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv sval
     sval' <- liftIO $ instantiateSetupValue sc s sval
     lval  <- liftIO $ resolveSetupVal cc m tyenv nameEnv sval' `X.catch` handleException opts
     return (memTy, lval)

injectJVMVal :: Sym -> JVMVal -> Crucible.RegValue Sym CJ.JVMValueType
injectJVMVal sym jv =
  case jv of
    RVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagR x
    IVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagI x
    LVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagL x

projectJVMVal :: Sym -> J.Type -> String -> Crucible.RegValue Sym CJ.JVMValueType -> IO JVMVal
projectJVMVal sym ty msg' v =
  case ty of
    J.BooleanType -> err -- FIXME
    J.ByteType    -> err -- FIXME
    J.CharType    -> err -- FIXME
    J.ShortType   -> err -- FIXME
    J.IntType     -> IVal <$> proj v CJ.tagI
    J.LongType    -> LVal <$> proj v CJ.tagL
    J.FloatType   -> err -- FIXME
    J.DoubleType  -> err -- FIXME
    J.ArrayType{} -> RVal <$> proj v CJ.tagR
    J.ClassType{} -> RVal <$> proj v CJ.tagR
  where
    proj ::
      forall tp.
      Crucible.RegValue Sym CJ.JVMValueType ->
      Ctx.Index CJ.JVMValueCtx tp ->
      IO (Crucible.RegValue Sym tp)
    proj val idx = Crucible.readPartExpr sym (Crucible.unVB (val Ctx.! idx)) msg

    msg = Crucible.GenericSimError $ "Ill-formed value for type " ++ show ty ++ " (" ++ msg' ++ ")"
    err = Crucible.addFailedAssertion sym msg

decodeJVMVal :: J.Type -> Crucible.AnyValue Sym -> Maybe JVMVal
decodeJVMVal ty v =
  case ty of
    J.BooleanType -> go v CJ.intRepr IVal
    J.ByteType    -> Nothing -- FIXME
    J.CharType    -> Nothing -- FIXME
    J.ShortType   -> Nothing -- FIXME
    J.IntType     -> go @CJ.JVMIntType v CJ.intRepr IVal
    J.LongType    -> go @CJ.JVMLongType v CJ.longRepr LVal
    J.FloatType   -> Nothing -- FIXME
    J.DoubleType  -> Nothing -- FIXME
    J.ArrayType{} -> go @CJ.JVMRefType v CJ.refRepr RVal
    J.ClassType{} -> go @CJ.JVMRefType v CJ.refRepr RVal
  where
    go ::
      forall t.
      Crucible.AnyValue Sym ->
      Crucible.TypeRepr t ->
      (Crucible.RegValue Sym t -> JVMVal) ->
      Maybe JVMVal
    go (Crucible.AnyValue repr rv) repr' k =
      case testEquality repr repr' of
        Just Refl -> Just (k rv)
        Nothing   -> Nothing

------------------------------------------------------------------------

asRVal :: W4.ProgramLoc -> JVMVal -> OverrideMatcher JVMRefVal
asRVal _ (RVal ptr) = return ptr
asRVal loc _ = failure loc BadPointerCast

------------------------------------------------------------------------
-- JVM OverrideSim operations

doFieldStore ::
  Sym ->
  Crucible.SymGlobalState Sym ->
  JVMRefVal ->
  String {- ^ field name -} ->
  JVMVal ->
  IO (Crucible.SymGlobalState Sym)
doFieldStore sym globals ref fname val =
  do let msg1 = Crucible.GenericSimError "Field store: null reference"
     ref' <- Crucible.readPartExpr sym ref msg1
     obj <- EvalStmt.readRef sym CJ.jvmIntrinsicTypes objectRepr ref' globals
     let msg2 = Crucible.GenericSimError "Field store: object is not a class instance"
     inst <- Crucible.readPartExpr sym (Crucible.unVB (Crucible.unroll obj Ctx.! Ctx.i1of2)) msg2
     let tab = Crucible.unRV (inst Ctx.! Ctx.i1of2)
     let tab' = Map.insert (Text.pack fname) (W4.justPartExpr sym (injectJVMVal sym val)) tab
     let inst' = Control.Lens.set (ixF Ctx.i1of2) (Crucible.RV tab') inst
     let obj' = Crucible.RolledType (Crucible.injectVariant sym knownRepr Ctx.i1of2 inst')
     EvalStmt.alterRef sym CJ.jvmIntrinsicTypes objectRepr ref' (W4.justPartExpr sym obj') globals

doArrayStore ::
  Sym ->
  Crucible.SymGlobalState Sym ->
  JVMRefVal ->
  Int {- ^ array index -} ->
  JVMVal ->
  IO (Crucible.SymGlobalState Sym)
doArrayStore sym globals ref idx val =
  do let msg1 = Crucible.GenericSimError "Array store: null reference"
     ref' <- Crucible.readPartExpr sym ref msg1
     obj <- EvalStmt.readRef sym CJ.jvmIntrinsicTypes objectRepr ref' globals
     let msg2 = Crucible.GenericSimError "Object is not an array"
     arr <- Crucible.readPartExpr sym (Crucible.unVB (Crucible.unroll obj Ctx.! Ctx.i2of2)) msg2
     let vec = Crucible.unRV (arr Ctx.! Ctx.i2of3)
     let vec' = vec V.// [(idx, injectJVMVal sym val)]
     let arr' = Control.Lens.set (ixF Ctx.i2of3) (Crucible.RV vec') arr
     let obj' = Crucible.RolledType (Crucible.injectVariant sym knownRepr Ctx.i2of2 arr')
     EvalStmt.alterRef sym CJ.jvmIntrinsicTypes objectRepr ref' (W4.justPartExpr sym obj') globals

doFieldLoad ::
  Sym ->
  W4.ProgramLoc ->
  Crucible.SymGlobalState Sym ->
  J.Type -> JVMRefVal -> String {- ^ field name -} -> IO JVMVal
doFieldLoad sym loc globals ty ref fname =
  do let msg1 = Crucible.GenericSimError "Field load: null reference"
     ref' <- Crucible.readPartExpr sym ref msg1
     obj <- EvalStmt.readRef sym CJ.jvmIntrinsicTypes objectRepr ref' globals
     let msg2 = Crucible.GenericSimError "Field load: object is not a class instance"
     inst <- Crucible.readPartExpr sym (Crucible.unVB (Crucible.unroll obj Ctx.! Ctx.i1of2)) msg2
     let tab = Crucible.unRV (inst Ctx.! Ctx.i1of2)
     let msg3 = Crucible.GenericSimError $ "Field load: field not found: " ++ fname
     let key = Text.pack fname
     val <- Crucible.readPartExpr sym (fromMaybe W4.Unassigned (Map.lookup key tab)) msg3
     projectJVMVal sym ty ("field load " ++ fname ++ ", " ++ show loc) val

doArrayLoad ::
  Sym ->
  W4.ProgramLoc ->
  Crucible.SymGlobalState Sym ->
  J.Type -> JVMRefVal -> Int {- ^ array index -} -> IO JVMVal
doArrayLoad sym loc globals ty ref idx =
  do let msg1 = Crucible.GenericSimError "Array load: null reference"
     ref' <- Crucible.readPartExpr sym ref msg1
     obj <- EvalStmt.readRef sym CJ.jvmIntrinsicTypes objectRepr ref' globals
     -- TODO: define a 'projectVariant' function in the OverrideSim monad
     let msg2 = Crucible.GenericSimError "Array load: object is not an array"
     arr <- Crucible.readPartExpr sym (Crucible.unVB (Crucible.unroll obj Ctx.! Ctx.i2of2)) msg2
     let vec = Crucible.unRV (arr Ctx.! Ctx.i2of3)
     let msg3 = Crucible.GenericSimError $ "Array load: index out of bounds: " ++ show idx
     val <-
       case vec V.!? idx of
         Just val -> return val
         Nothing -> Crucible.addFailedAssertion sym msg3
     projectJVMVal sym ty ("array load " ++ show idx ++ ", " ++ show loc) val

doAllocateObject ::
  Sym ->
  Crucible.HandleAllocator RealWorld ->
  CJ.JVMContext ->
  J.ClassName ->
  Crucible.SymGlobalState Sym ->
  IO (JVMRefVal, Crucible.SymGlobalState Sym)
doAllocateObject sym halloc jc cname globals =
  do cls <- getJVMClassByName sym globals jc cname
     let fieldIds = fieldsOfClassName jc cname
     let pval = W4.justPartExpr sym unassignedJVMValue
     let fields = Map.fromList [ (CJ.fieldIdText f, pval) | f <- fieldIds ]
     let inst = Ctx.Empty Ctx.:> Crucible.RV fields Ctx.:> Crucible.RV cls
     let repr = Ctx.Empty Ctx.:> instanceRepr Ctx.:> arrayRepr
     let obj = Crucible.RolledType (Crucible.injectVariant sym repr Ctx.i1of2 inst)
     ref <- stToIO (Crucible.freshRefCell halloc objectRepr)
     let globals' = Crucible.updateRef ref (W4.justPartExpr sym obj) globals
     return (W4.justPartExpr sym (Crucible.toMuxTree sym ref), globals')

doAllocateArray ::
  Sym ->
  Crucible.HandleAllocator RealWorld ->
  CJ.JVMContext -> Int -> J.Type ->
  Crucible.SymGlobalState Sym ->
  IO (JVMRefVal, Crucible.SymGlobalState Sym)
doAllocateArray sym halloc jc len elemTy globals =
  do len' <- liftIO $ W4.bvLit sym CJ.w32 (toInteger len)
     let vec = V.replicate len unassignedJVMValue
     rep <- makeJVMTypeRep sym globals jc elemTy
     let arr = Ctx.Empty Ctx.:> Crucible.RV len' Ctx.:> Crucible.RV vec Ctx.:> Crucible.RV rep
     let repr = Ctx.Empty Ctx.:> instanceRepr Ctx.:> arrayRepr
     let obj = Crucible.RolledType (Crucible.injectVariant sym repr Ctx.i2of2 arr)
     ref <- stToIO (Crucible.freshRefCell halloc objectRepr)
     let globals' = Crucible.updateRef ref (W4.justPartExpr sym obj) globals
     return (W4.justPartExpr sym (Crucible.toMuxTree sym ref), globals')

doResolveGlobal :: Sym -> () -> String -> IO JVMRefVal
doResolveGlobal _sym _mem _name = fail "doResolveGlobal: FIXME"
-- FIXME: replace () with whatever type we need to look up global/static references

-- | Lookup the data structure associated with a class.
getJVMClassByName ::
  Sym ->
  Crucible.SymGlobalState Sym ->
  CJ.JVMContext ->
  J.ClassName ->
  IO (Crucible.RegValue Sym CJ.JVMClassType)
getJVMClassByName sym globals jc cname =
  do let key = CJ.classNameText cname
     let msg1 = Crucible.GenericSimError "Class table not found"
     let msg2 = Crucible.GenericSimError $ "Class was not found in class table: " ++ J.unClassName cname
     classtab <-
       case Crucible.lookupGlobal (CJ.dynamicClassTable jc) globals of
         Just x -> return x
         Nothing -> Crucible.addFailedAssertion sym msg1
     let pcls = fromMaybe W4.Unassigned (Map.lookup key classtab)
     Crucible.readPartExpr sym pcls msg2

objectRepr :: Crucible.TypeRepr CJ.JVMObjectType
objectRepr = knownRepr

arrayRepr :: Crucible.TypeRepr CJ.JVMArrayType
arrayRepr = knownRepr

instanceRepr :: Crucible.TypeRepr CJ.JVMInstanceType
instanceRepr = knownRepr

-- | A degenerate value of the variant type, where every branch is
-- unassigned. This is used to model uninitialized array elements.
unassignedJVMValue :: Crucible.RegValue sym CJ.JVMValueType
unassignedJVMValue =
  Ctx.fmapFC (\_ -> Crucible.VB W4.Unassigned) (knownRepr :: Crucible.CtxRepr CJ.JVMValueCtx)

mkFieldId :: J.Class -> J.Field -> J.FieldId
mkFieldId c f = J.FieldId (J.className c) (J.fieldName f) (J.fieldType f)

-- | Find the fields not just in this class, but also in the super classes.
fieldsOfClass :: CJ.JVMContext -> J.Class -> [J.FieldId]
fieldsOfClass jc cls =
  case J.superClass cls of
    Nothing -> fields
    Just super -> fields ++ fieldsOfClassName jc super
  where
    fields = map (mkFieldId cls) (J.classFields cls)

fieldsOfClassName :: CJ.JVMContext -> J.ClassName -> [J.FieldId]
fieldsOfClassName jc cname =
  case Map.lookup cname (CJ.classTable jc) of
    Just cls -> fieldsOfClass jc cls
    Nothing -> []

-- | Given a JVM type, generate a runtime value for its representation.
makeJVMTypeRep ::
  Sym ->
  Crucible.SymGlobalState Sym ->
  CJ.JVMContext ->
  J.Type ->
  IO (Crucible.RegValue Sym CJ.JVMTypeRepType)
makeJVMTypeRep sym globals jc ty =
  case ty of
    J.ArrayType ety ->
      do ety' <- makeJVMTypeRep sym globals jc ety
         return $ Crucible.RolledType (Crucible.injectVariant sym knownRepr Ctx.i1of3 ety')
    J.ClassType _cn ->
      primTypeRep 8 -- FIXME: temporary hack
    J.BooleanType -> primTypeRep 0
    J.ByteType    -> primTypeRep 1
    J.CharType    -> primTypeRep 2
    J.DoubleType  -> primTypeRep 3
    J.FloatType   -> primTypeRep 4
    J.IntType     -> primTypeRep 5
    J.LongType    -> primTypeRep 6
    J.ShortType   -> primTypeRep 7
  where
    primTypeRep n =
      do n' <- W4.bvLit sym CJ.w32 n
         return $ Crucible.RolledType (Crucible.injectVariant sym knownRepr Ctx.i3of3 n')
