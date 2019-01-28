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
  ) where

import           Control.Lens
import           Control.Exception as X
import           Control.Monad.ST (RealWorld, stToIO)
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class
import           Control.Monad.IO.Class
import           Control.Monad
import           Data.Foldable (for_, traverse_)
import           Data.List (tails)
import           Data.IORef (readIORef, writeIORef, newIORef, IORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (fromMaybe)
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified Data.Vector as V

-- cryptol
import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)

-- what4
import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4
--import qualified What4.Expr.Builder as W4
--import qualified What4.Symbol as W4
import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4

-- crucible
import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.SAWCore as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible (TypeRepr(UnitRepr), GlobalVar)
import qualified Lang.Crucible.FunctionHandle as Crucible (HandleAllocator, freshRefCell)
import qualified Lang.Crucible.Simulator as Crucible
import qualified Lang.Crucible.Simulator.EvalStmt as EvalStmt (readRef, alterRef)
--import qualified Lang.Crucible.Simulator.OverrideSim as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
--import qualified Lang.Crucible.Simulator.RegMap as Crucible
--import qualified Lang.Crucible.Simulator.SimError as Crucible
import qualified Lang.Crucible.Types as Crucible
import qualified Lang.Crucible.Utils.MuxTree as Crucible (toMuxTree)

-- crucible-jvm
import qualified Lang.Crucible.JVM.Translation as CJ

-- parameterized-utils
import           Data.Parameterized.Classes ((:~:)(..), testEquality, knownRepr, ixF)
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
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
  --- | BadSymType Crucible.SymType
  | BadTermMatch Term Term -- ^ simulated and specified terms did not match
  | BadPointerCast -- ^ Pointer required to process points-to
  | BadReturnSpecification -- ^ type mismatch in return specification
  | NonlinearPatternNotSupported
  | BadPointerLoad String -- ^ loadRaw failed due to type error
  | StructuralMismatch JVMVal
                       SetupValue
                       J.Type
                        -- ^ simulated value, specified value, specified type
  deriving Show

data OverrideFailure = OF W4.ProgramLoc OverrideFailureReason
  deriving Show

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
--   the @methodSpecHandler1@ function.  In order to implement selecting
--   between the different method specs, we invent a collection of boolean
--   selector variables, one for each spec.  We branch on each boolean variable
--   in turn, performing memory updates and computing conditions inside each
--   branch.  Inside each branch, the postconditions for each spec are assumed.
--   However, in order to correctly handle preconditions, we need to do some special
--   bookkeeping.  In each branch, we compute and stash away the associated precondition.
--   Later, /after/ all the branches have merged, we assume, for each branch, that
--   the associated selector variable is equal to the precondition for that branch.
--
--   Let the selector variable for branch @n@ be @a_n@, the precondition be @P_n@,
--   the postcondition be @Q_n@ and the result be @r_n@.  The end result is that
--   we assume @a_n = P_n@ and @a_n -> Q_n@ for each @n@.
--   Moreover, the computed result (and global variables) will be constructed as
--   a merge tree, e.g., @if a_0 r_0 else (if a_1 r_1 else r_2)@.
--   Finally we must assert that one of the branches is taken, i.e., that
--   @a_1 or a_2 or ... or a_n@.
--
--   The overall result should be a \"left biased\" selection of specifications,
--   where specs appearing earlier in the list will be prefered to later specs.
--
--   The strange bookkeeping tricks used below are necessary because we calculate
--   the precondition for the branches at the same time as we compute the memory
--   updates and return result.  To make the merge accounting work out, we need to
--   already be inside a branch when we do those computations.  Thus, we invent
--   fresh variables and then later \"bind\" them with equality assumptions, after
--   all the merging is computed.
methodSpecHandler ::
  forall rtp args ret.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext          {- ^ context for interacting with Crucible        -} ->
  [CrucibleMethodSpecIR]   {- ^ specification for current function override  -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  Crucible.OverrideSim (Crucible.SAWCruciblePersonality Sym) Sym CJ.JVM rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler opts sc cc css retTy = do
  sym <- Crucible.getSymInterface
  let jc = cc^.ccJVMContext
  top_loc <- liftIO $ W4.getCurrentProgramLoc sym

  -- Invent the necessary selector variables and set up the precondition IORefs.
  branches <- forM (zip css [0::Int .. ]) $ \(cs,i) -> liftIO $
                do let pnm = "lemma_" ++ show i ++ "_" ++ (cs^.csName)
                   Right smb <- return $ W4.userSymbol pnm
                   p <- W4.freshConstant sym smb W4.BaseBoolRepr
                   preCondRef <- newIORef Nothing
                   return (p, cs, preCondRef)

  -- This internal function runs a single method spec. Note we are careful to avoid
  -- any abort conditions.  As this might cause us to unwind past the code that assembles
  -- and asserts the preconditions.  Instead we use a Maybe return value to encode the
  -- partiality involved in selecting among the overrides.
  let runSpec :: forall rtp'.
        CrucibleMethodSpecIR {- spec to run -} ->
        IORef (Maybe [(W4.Pred Sym, Crucible.SimError)]) {- IORef to hold the computed precondition -} ->
        Crucible.OverrideSim (Crucible.SAWCruciblePersonality Sym) Sym CJ.JVM rtp' args
              (Crucible.MaybeType ret)
              (Crucible.RegValue Sym (Crucible.MaybeType ret))
      runSpec cs preCondRef =
        do
        g <- Crucible.readGlobals
        Crucible.RegMap args <- Crucible.getOverrideArgs
        let initialFree = Set.fromList (map (termId . ttTerm)
                                       (view (csPreState.csFreshVars) cs))
        res <- liftIO $ runOverrideMatcher sym g Map.empty Map.empty initialFree (cs^.csLoc)
                           (methodSpecHandler1 opts sc cc jc args retTy cs)
        case res of
          Left _err ->
            do Crucible.overrideReturn' (Crucible.RegEntry (Crucible.MaybeRepr retTy) W4.Unassigned)
          Right (retVal, st) ->
            do let loc = st^.osLocation
               liftIO $ writeIORef preCondRef (Just (st^.osAsserts))
               forM_ (st^.osAssumes) $ \asum ->
                  let rsn = Crucible.AssumptionReason loc "override postcondition" in
                  liftIO $ Crucible.addAssumption (cc^.ccBackend)
                             (Crucible.LabeledPred asum rsn)
               let g' = st^.overrideGlobals
               Crucible.writeGlobals g'
               Crucible.overrideReturn' (Crucible.RegEntry (Crucible.MaybeRepr retTy) (W4.justPartExpr sym retVal))

  -- Set up a fresh call frame to contain the branching and force a merge point.
  -- Run each method spec in a separate branch, with a final default branch that
  -- returns @Nothing@ to indicate the case when no override applies.
  ret <- Crucible.callOverride
            (Crucible.mkOverride' "overrideBranches" (Crucible.MaybeRepr retTy)
               (Crucible.symbolicBranches Crucible.emptyRegMap $
                 [ (p,runSpec cs preCondRef, Just (W4.plSourceLoc (cs^.csLoc)))
                 | (p,cs,preCondRef) <- branches
                 ]
                 ++ [(W4.truePred sym, return W4.Unassigned, Nothing)]
                 ))
            =<< Crucible.getOverrideArgs

  liftIO $
        -- Add the assumptions that bind the invented selector variables to the computed
        -- preconditions
     do forM_ branches $ \(p,_,preCondRef) ->
              do readIORef preCondRef >>= \case
                   -- No precondition computed, equlivalant to false
                   Nothing ->
                     do np <- W4.notPred sym p
                        Crucible.addAssumption (cc^.ccBackend) (Crucible.LabeledPred np
                           (Crucible.AssumptionReason top_loc "failed override branch"))
                   -- Take the conjunction of all preconditions, and equate them to
                   -- the selector variable
                   Just ps ->
                     do allps <- conjunction sym $ map (view _1) ps
                        eqp   <- W4.eqPred sym p allps
                        Crucible.addAssumption (cc^.ccBackend) (Crucible.LabeledPred eqp
                              (Crucible.AssumptionReason top_loc "override selector"))

        -- Now, assert each of the preconditions from each branch separately, but weaken them
        -- each by the disjunction of all the other selector variables.  This preserves the original
        -- metadata associated with the precondition, but is still a necessary condition in
        -- the overall proof.  The added disjunctions allow for the possibility that other override
        -- specifications will be chosen instead of this one.
        forM_ (zip branches (dropith $ map (view _1) branches)) $ \((_,_,preCondRef), otherps) ->
              do readIORef preCondRef >>= \case
                   Nothing -> return ()
                   Just ps ->
                        forM_ ps $ \(pcond,rsn) ->
                          do pcond' <- disjunction sym (pcond : otherps)
                             Crucible.addAssertion (cc^.ccBackend) (Crucible.LabeledPred pcond' rsn)

        -- Now project the mabye value we defined above.  This has the effect of asserting that
        -- _some_ override was chosen.
        let fsym = (head css)^.csName
        Crucible.readPartExpr sym (Crucible.regValue ret)
          (Crucible.AssertFailureSimError ("No applicable override for " ++ fsym))


dropith :: [a] -> [[a]]
dropith [] = []
dropith (a:as) = as : map (a:) (dropith as)


-- | Compute the conjunction of a set of predicates.
conjunction :: Foldable t => Sym -> t (W4.Pred Sym) -> IO (W4.Pred Sym)
conjunction sym = foldM (W4.andPred sym) (W4.truePred sym)

-- | Compute the disjunction of a set of predicates.
disjunction :: Foldable t => Sym -> t (W4.Pred Sym) -> IO (W4.Pred Sym)
disjunction sym = foldM (W4.orPred sym) (W4.falsePred sym)

------------------------------------------------------------------------

-- | Use a method spec to override the behavior of a function.
-- That is: match the current state using the pre-condition,
-- and execute the post condition.
methodSpecHandler1 ::
  forall ret ctx.
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext          {- ^ context for interacting with Crucible        -} ->
  CJ.JVMContext            {- ^ context for interacting with Crucible-JVM    -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
                           {- ^ the arguments to the function -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher (Crucible.RegValue Sym ret)
methodSpecHandler1 opts sc cc jc args retTy cs =
  do let expectedArgTypes = {-(traverse . _1) resolveMemType-} (Map.elems (cs^.csArgBindings))

     sym <- getSymInterface

     let aux ::
           (J.Type, SetupValue) -> Crucible.AnyValue Sym ->
           OverrideMatcher (JVMVal, J.Type, SetupValue)
         aux (argTy, setupVal) val =
           case decodeJVMVal argTy val of
             Just val' -> return (val', argTy, setupVal)
             Nothing -> fail "unexpected type"

     -- todo: fail if list lengths mismatch
     xs <- zipWithM aux expectedArgTypes (assignmentToList args)

     sequence_ [ matchArg sc cc (cs^.csLoc) PreState x y z | (x, y, z) <- xs ]

     learnCond opts sc cc cs PreState (cs^.csPreState)

     executeCond opts sc cc jc cs (cs^.csPostState)

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
  CJ.JVMContext ->
  CrucibleMethodSpecIR ->
  StateSpec ->
  OverrideMatcher ()
executeCond opts sc cc jc cs ss =
  do refreshTerms sc ss
     traverse_ (executeAllocation opts cc jc) (Map.assocs (ss^.csAllocs))
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
enforceDisjointness cc loc ss =
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

--          do t <- liftIO $ scEq sc old val
--             p <- liftIO $ resolveSAWPred cc t
--             addAssert p (Crucible.AssertFailureSimError ("literal equality " ++ stateCond prepost))


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
  = do sym      <- getSymInterface
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
valueToSC sym loc failMsg Cryptol.TVBit (IVal x) =
  liftIO (Crucible.toSC sym x) -- TODO: is this right?

valueToSC sym loc failMsg (Cryptol.TVSeq _n Cryptol.TVBit) (IVal x) =
  liftIO (Crucible.toSC sym x)

valueToSC sym loc failMsg (Cryptol.TVSeq _n Cryptol.TVBit) (LVal x) =
  liftIO (Crucible.toSC sym x)

valueToSC _sym loc failMsg _tval _val =
  failure loc failMsg
-- TODO: check sizes on bitvectors, support bool, char, and short types

------------------------------------------------------------------------

--typeToSC :: SharedContext -> Crucible.Type -> IO Term
--typeToSC sc t =
--  case Crucible.typeF t of
--    Crucible.Bitvector sz -> scBitvector sc (fromInteger (Crucible.bytesToBits sz))
--    Crucible.Float -> fail "typeToSC: float not supported"
--    Crucible.Double -> fail "typeToSC: double not supported"
--    Crucible.Array sz ty ->
--      do n <- scNat sc (fromIntegral sz)
--         ty' <- typeToSC sc ty
--         scVecType sc n ty'
--    Crucible.Struct fields ->
--      do fields' <- V.toList <$> traverse (typeToSC sc . view Crucible.fieldVal) fields
--         scTuple sc fields'

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
            p <- liftIO $ resolveSAWPred cc t
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
      do (ty, val') <- resolveSetupValueJVM opts cc sc spec val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         sym <- getSymInterface
         globals <- OM (use overrideGlobals)
         v <- liftIO $ doFieldLoad sym globals ty rval fname
         matchArg sc cc loc prepost v ty val

    PointsToElem loc ptr idx val ->
      do (ty, val') <- resolveSetupValueJVM opts cc sc spec val
         (_, ptr') <- resolveSetupValueJVM opts cc sc spec ptr
         rval <- asRVal loc ptr'
         sym <- getSymInterface
         globals <- OM (use overrideGlobals)
         v <- liftIO $ doArrayLoad sym globals ty rval idx
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
     p <- liftIO $ resolveSAWPred cc u
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
  CJ.JVMContext                  ->
  (AllocIndex, (W4.ProgramLoc, Allocation)) ->
  OverrideMatcher ()
executeAllocation opts cc jc (var, (loc, alloc)) =
  do liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show alloc]
     sym <- getSymInterface
     globals <- OM (use overrideGlobals)
     halloc <- error "halloc"
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
     p <- liftIO $ resolveSAWPred cc t
     addAssume p

------------------------------------------------------------------------

-- | Construct a completely symbolic pointer. This pointer could point to anything, or it could
-- be NULL.
--executeFreshPointer ::
--  CrucibleContext {- ^ Crucible context       -} ->
--  AllocIndex      {- ^ SetupVar allocation ID -} ->
--  IO JVMRefVal {- ^ Symbolic pointer value -}
--executeFreshPointer cc (AllocIndex i) =
--  do let mkName base = W4.systemSymbol (base ++ show i ++ "!")
--         sym         = cc^.ccBackend
--     blk <- W4.freshConstant sym (mkName "blk") W4.BaseNatRepr
--     off <- W4.freshConstant sym (mkName "off") (W4.BaseBVRepr Crucible.PtrWidth)
--     return (Crucible.LLVMPointer blk off)

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
    -- SetupStruct vs -> SetupStruct <$> mapM (instantiateSetupValue sc s) vs
    -- SetupArray  vs -> SetupArray <$> mapM (instantiateSetupValue sc s) vs
    -- SetupElem _ _  -> return v
    -- SetupField _ _ -> return v
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

--resolveSetupValue ::
--  Options              ->
--  CrucibleContext      ->
--  SharedContext        ->
--  CrucibleMethodSpecIR ->
--  SetupValue           ->
--  OverrideMatcher (J.Type, Crucible.RegValue Sym CJ.JVMValueType)
--resolveSetupValue opts cc sc spec sval =
--  do (memTy, lval) <- resolveSetupValueJVM opts cc sc spec sval
--     sym <- getSymInterface
--     let aval = encodeJVMVal sym lval
--     return (memTy, aval)

injectJVMVal :: Sym -> JVMVal -> Crucible.RegValue Sym CJ.JVMValueType
injectJVMVal sym jv =
  case jv of
    RVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagR x
    IVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagI x
    LVal x -> Crucible.injectVariant sym W4.knownRepr CJ.tagL x

projectJVMVal :: Sym -> J.Type -> Crucible.RegValue Sym CJ.JVMValueType -> IO JVMVal
projectJVMVal sym ty v =
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

    msg = Crucible.GenericSimError "Ill-formed value for type"
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

--asRVal ::
--  W4.ProgramLoc ->
--  (J.Type, Crucible.AnyValue Sym) ->
--  OverrideMatcher (String, JVMRefVal)
--asRVal _ (JavaClass cname, RVal ptr) = return (cname, ptr)
--asRVal loc _ = failure loc BadPointerCast

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
  Crucible.SymGlobalState Sym ->
  J.Type -> JVMRefVal -> String {- ^ field name -} -> IO JVMVal
doFieldLoad sym globals ty ref fname =
  do let msg1 = Crucible.GenericSimError "Field load: null reference"
     ref' <- Crucible.readPartExpr sym ref msg1
     obj <- EvalStmt.readRef sym CJ.jvmIntrinsicTypes objectRepr ref' globals
     let msg2 = Crucible.GenericSimError "Field load: object is not a class instance"
     inst <- Crucible.readPartExpr sym (Crucible.unVB (Crucible.unroll obj Ctx.! Ctx.i1of2)) msg2
     let tab = Crucible.unRV (inst Ctx.! Ctx.i1of2)
     let msg3 = Crucible.GenericSimError $ "Field load: field not found: " ++ fname
     let key = Text.pack fname
     val <- Crucible.readPartExpr sym (fromMaybe W4.Unassigned (Map.lookup key tab)) msg3
     projectJVMVal sym ty val

doArrayLoad ::
  Sym ->
  Crucible.SymGlobalState Sym ->
  J.Type -> JVMRefVal -> Int {- ^ array index -} -> IO JVMVal
doArrayLoad sym globals ty ref idx =
  do let msg1 = Crucible.GenericSimError "Field load: null reference"
     ref' <- Crucible.readPartExpr sym ref msg1
     obj <- EvalStmt.readRef sym CJ.jvmIntrinsicTypes objectRepr ref' globals
     -- TODO: define a 'projectVariant' function in the OverrideSim monad
     let msg2 = Crucible.GenericSimError "Array load: object is not an array"
     arr <- Crucible.readPartExpr sym (Crucible.unVB (Crucible.unroll obj Ctx.! Ctx.i2of2)) msg2
     let vec = Crucible.unRV (arr Ctx.! Ctx.i2of3)
     let msg3 = Crucible.GenericSimError $ "Field load: index out of bounds: " ++ show idx
     val <-
       case vec V.!? idx of
         Just val -> return val
         Nothing -> Crucible.addFailedAssertion sym msg3
     projectJVMVal sym ty val

doAllocateObject ::
  Sym ->
  Crucible.HandleAllocator RealWorld ->
  CJ.JVMContext ->
  J.ClassName ->
  Crucible.SymGlobalState Sym ->
  IO (JVMRefVal, Crucible.SymGlobalState Sym)
doAllocateObject sym halloc jc cname globals =
  do --cls <- getJVMClassByName sym globals jc cname
     let fieldIds = fieldsOfClassName jc cname
     let pval = W4.justPartExpr sym unassignedJVMValue
     let fields = Map.fromList [ (Text.pack (CJ.fieldIdString f), pval) | f <- fieldIds ]
     cls <- dummyClassObject sym cname -- FIXME: temporary hack
     let inst = Ctx.Empty Ctx.:> Crucible.RV fields Ctx.:> Crucible.RV cls
     let repr = Ctx.Empty Ctx.:> instanceRepr Ctx.:> arrayRepr
     let obj = Crucible.RolledType (Crucible.injectVariant sym repr Ctx.i1of2 inst)
     ref <- stToIO (Crucible.freshRefCell halloc objectRepr)
     let globals' = Crucible.updateRef ref (W4.justPartExpr sym obj) globals
     return (W4.justPartExpr sym (Crucible.toMuxTree sym ref), globals')

dummyClassObject ::
  Sym -> J.ClassName -> IO (Crucible.RegValue Sym CJ.JVMClassType)
dummyClassObject sym cname =
  do name <- W4.stringLit sym (Text.pack (J.unClassName cname))
     status <- W4.bvLit sym knownRepr 0
     let super = W4.Unassigned
     let methods = Map.empty
     let interfaces = V.empty
     return $
       Crucible.RolledType $
       Ctx.Empty
       Ctx.:> Crucible.RV name
       Ctx.:> Crucible.RV status
       Ctx.:> Crucible.RV super
       Ctx.:> Crucible.RV methods
       Ctx.:> Crucible.RV interfaces

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

--type JVMRefType = MaybeType (ReferenceType JVMObjectType)
--RegValue sym (MaybeType tp) = PartExpr (Pred sym) (RegValue sym tp)
--RegValue sym (ReferenceType a) = MuxTree sym (RefCell a)

-- | Lookup the data structure associated with a class.
getJVMClassByName ::
  Sym ->
  Crucible.SymGlobalState Sym ->
  CJ.JVMContext ->
  J.ClassName ->
  IO (Crucible.RegValue Sym CJ.JVMClassType)
getJVMClassByName sym globals jc cname =
  do let key = Text.pack (J.unClassName cname)
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
    J.ClassType cn ->
      primTypeRep 8 -- FIXME: temporary hack
{-
      do cls <- getJVMClassByName sym globals jc cn
         return $ Crucible.RolledType (Crucible.injectVariant sym knownRepr Ctx.i2of3 cls)
-}
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

