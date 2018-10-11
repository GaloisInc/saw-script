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
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ViewPatterns #-}

module SAWScript.CrucibleOverride
  ( OverrideMatcher(..)
  , runOverrideMatcher

  , setupValueSub
  , executeFreshPointer
  , osAsserts
  , termSub

  , learnCond
  , matchArg
  , methodSpecHandler
  , valueToSC
  , termId
  ) where

import           Control.Lens
import           Control.Exception as X
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class
import           Control.Monad.IO.Class
import           Control.Monad
import           Data.Either (partitionEithers)
import           Data.Foldable (for_, traverse_)
import           Data.List (tails)
import           Data.IORef (readIORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Text.LLVM.AST as L

import qualified Cryptol.TypeCheck.AST as Cryptol (Schema(..))
import qualified Cryptol.Eval.Type as Cryptol (TValue(..), evalType)
import qualified Cryptol.Utils.PP as Cryptol

import qualified Lang.Crucible.Backend as Crucible
import qualified Lang.Crucible.Backend.SAWCore as Crucible
import qualified Lang.Crucible.CFG.Core as Crucible
                   (TypeRepr(UnitRepr), GlobalVar)
import qualified Lang.Crucible.Simulator.OverrideSim as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible
--import qualified Lang.Crucible.Types as Crucible

import qualified What4.BaseTypes as W4
import qualified What4.Interface as W4
import qualified What4.Expr.Builder as W4
import qualified What4.Symbol as W4
--import qualified What4.Partial as W4
import qualified What4.ProgramLoc as W4

import qualified SAWScript.CrucibleLLVM as Crucible

import           Data.Parameterized.Classes ((:~:)(..), testEquality)
import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Data.Parameterized.Context as Ctx

import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Prelude (scEq)
import           Verifier.SAW.TypedAST
--import           Verifier.SAW.Term.Pretty
import           Verifier.SAW.Recognizer
import           Verifier.SAW.TypedTerm

import           SAWScript.CrucibleMethodSpecIR
import           SAWScript.CrucibleResolveSetupValue
import           SAWScript.Options
import           SAWScript.Utils (handleException)

-- | The 'OverrideMatcher' type provides the operations that are needed
-- to match a specification's arguments with the arguments provided by
-- the Crucible simulation in order to compute the variable substitution
-- and side-conditions needed to proceed.
newtype OverrideMatcher arch mode a =
  OM (StateT (OverrideState arch) (ExceptT OverrideFailure IO) a)
  deriving (Functor, Applicative, Monad, MonadIO)

data OverrideState arch = OverrideState
  { -- | Substitution for memory allocations
    _setupValueSub :: Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch))

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
  | StructuralMismatch (Crucible.LLVMVal Sym)
                       SetupValue
                       Crucible.MemType
                        -- ^ simulated value, specified value, specified type

ppOverrideFailureReason :: OverrideFailureReason -> PP.Doc
ppOverrideFailureReason rsn = case rsn of
  AmbiguousPointsTos pts ->
    PP.text "ambiguous collection of points-to assertions" PP.<$$>
    (PP.indent 2 $ PP.vcat (map ppPointsTo pts))
  AmbiguousVars vs ->
    PP.text "ambiguous collection of varaibles" PP.<$$>
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
    PP.indent 2 (Crucible.ppMemType ty)


ppTypedTerm :: TypedTerm -> PP.Doc
ppTypedTerm (TypedTerm tp tm) =
  ppTerm defaultPPOpts tm
  PP.<+> PP.text ":" PP.<+>
  PP.text (show (Cryptol.ppPrec 0 tp))

ppPointsTo :: PointsTo -> PP.Doc
ppPointsTo (PointsTo _loc ptr val) =
  ppSetupValue ptr PP.<+> PP.text "|->" PP.<+> ppSetupValue val

commaList :: [PP.Doc] -> PP.Doc
commaList []     = PP.empty
commaList (x:xs) = x PP.<> PP.hcat (map (\y -> PP.comma PP.<+> y) xs)

ppSetupValue :: SetupValue -> PP.Doc
ppSetupValue setupval = case setupval of
  SetupTerm tm   -> ppTypedTerm tm
  SetupVar i     -> PP.text ("@" ++ show i)
  SetupNull      -> PP.text "NULL"
  SetupStruct vs -> PP.braces (commaList (map ppSetupValue vs))
  SetupArray vs  -> PP.brackets (commaList (map ppSetupValue vs))
  SetupElem v i  -> PP.parens (ppSetupValue v) PP.<> PP.text ("." ++ show i)
  SetupField v f -> PP.parens (ppSetupValue v) PP.<> PP.text ("." ++ f)
  SetupGlobal nm -> PP.text ("global(" ++ nm ++ ")")
  SetupGlobalInitializer nm -> PP.text ("global_initializer(" ++ nm ++ ")")

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
  Sym                           {- ^ simulator                      -} ->
  Crucible.SymGlobalState Sym   {- ^ initial global variables       -} ->
  Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) {- ^ initial allocation substituion -} ->
  Map VarIndex Term             {- ^ initial term substituion       -} ->
  Set VarIndex                  {- ^ initial free terms             -} ->
  W4.ProgramLoc                 {- ^ location information for the override -} ->
  OverrideState arch
initialState sym globals allocs terms free loc = OverrideState
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
  OverrideMatcher arch md ()
addAssert p r = OM (osAsserts %= cons (p,r))

addAssume ::
  W4.Pred Sym       {- ^ property -} ->
  OverrideMatcher arch md ()
addAssume p = OM (osAssumes %= cons p)

data RO
data RW

readGlobal ::
  Crucible.GlobalVar tp ->
  OverrideMatcher arch md (Crucible.RegValue Sym tp)
readGlobal k =
  do mb <- OM (uses overrideGlobals (Crucible.lookupGlobal k))
     case mb of
       Nothing -> fail ("No such global: " ++ show k)
       Just v  -> return v

writeGlobal ::
  Crucible.GlobalVar    tp ->
  Crucible.RegValue Sym tp ->
  OverrideMatcher arch RW ()
writeGlobal k v = OM (overrideGlobals %= Crucible.insertGlobal k v)

------------------------------------------------------------------------

-- | Abort the current computation by raising the given 'OverrideFailure'
-- exception.
failure :: W4.ProgramLoc -> OverrideFailureReason -> OverrideMatcher arch md a
failure loc e = OM (lift (throwE (OF loc e)))

------------------------------------------------------------------------

-- | This function is responsable for implementing the \"override\" behavior
--   of method specifications.  The main work done in this function to manage
--   the process of selecting between several possible different override
--   specifications that could apply.  We want a proof to succeed if _any_
--   choice of method spec allows the proof to go through, which is a slightly
--   akward thing to fit into the symbolic simulation framework.
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
  forall arch rtp args ret.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  W4.ProgramLoc            {- ^ Location of the call site for error reporting-} ->
  [CrucibleMethodSpecIR]   {- ^ specification for current function override  -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  Crucible.OverrideSim (Crucible.SAWCruciblePersonality Sym) Sym (Crucible.LLVM arch) rtp args ret
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
  -- postconditions, update the crucible global varible state, and return the
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
         [ ( W4.truePred sym
           , liftIO $ Crucible.addFailedAssertion sym (Crucible.GenericSimError "no override specification applies")
           , Just (W4.plSourceLoc top_loc)
           )]
       ))
     (Crucible.RegMap args)

------------------------------------------------------------------------

-- | Use a method spec to override the behavior of a function.
--   This function computes the pre-state portion of the override,
--   which involves reading values from arguments and memory and computing
--   substitutions for the setup value variables, and computing precondition
--   predicates.
methodSpecHandler_prestate ::
  forall arch ctx.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
                           {- ^ the arguments to the function -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher arch RO ()
methodSpecHandler_prestate opts sc cc args cs =
    do let expectedArgTypes = {-(traverse . _1) resolveMemType-} (Map.elems (cs^.csArgBindings))

       sym <- getSymInterface

       let aux (memTy, setupVal) (Crucible.AnyValue tyrep val) =
             do storTy <- Crucible.toStorableType memTy
                pmv <- Crucible.packMemValue sym storTy tyrep val
                return (pmv, memTy, setupVal)

       -- todo: fail if list lengths mismatch
       xs <- liftIO (zipWithM aux expectedArgTypes (assignmentToList args))

       sequence_ [ matchArg sc cc (cs^.csLoc) PreState x y z | (x, y, z) <- xs]

       learnCond opts sc cc cs PreState (cs^.csPreState)


-- | Use a method spec to override the behavior of a function.
--   This function computes the post-state portion of the override,
--   which involves writing values into memory, computing the return value,
--   and computing postcondition predicates.
methodSpecHandler_poststate ::
  forall arch ret.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                  {- ^ output/verbosity options                     -} ->
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext arch     {- ^ context for interacting with Crucible        -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher arch RW (Crucible.RegValue Sym ret)
methodSpecHandler_poststate opts sc cc retTy cs =
  do executeCond opts sc cc cs (cs^.csPostState)
     computeReturnValue opts cc sc cs retTy (cs^.csRetValue)

-- learn pre/post condition
learnCond :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch))
          => Options
          -> SharedContext
          -> CrucibleContext arch
          -> CrucibleMethodSpecIR
          -> PrePost
          -> StateSpec
          -> OverrideMatcher arch md ()
learnCond opts sc cc cs prepost ss = do
  let loc = cs^.csLoc
  matchPointsTos opts sc cc cs prepost (ss^.csPointsTos)
  traverse_ (learnSetupCondition opts sc cc cs prepost) (ss^.csConditions)
  enforceDisjointness cc loc ss
  enforceCompleteSubstitution loc ss


-- | Verify that all of the fresh variables for the given
-- state spec have been "learned". If not, throws
-- 'AmbiguousVars' exception.
enforceCompleteSubstitution :: W4.ProgramLoc -> StateSpec -> OverrideMatcher arch md ()
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
executeCond :: (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch))
            => Options
            -> SharedContext
            -> CrucibleContext arch
            -> CrucibleMethodSpecIR
            -> StateSpec
            -> OverrideMatcher arch RW ()
executeCond opts sc cc cs ss = do
  refreshTerms sc ss

  ptrs <- liftIO $ Map.traverseWithKey
            (\k _memty -> executeFreshPointer cc k)
            (ss^.csFreshPointers)
  OM (setupValueSub %= Map.union ptrs)

  traverse_ (executeAllocation opts cc) (Map.assocs (ss^.csAllocs))
  traverse_ (executePointsTo opts sc cc cs) (ss^.csPointsTos)
  traverse_ (executeSetupCondition opts sc cc cs) (ss^.csConditions)


-- | Allocate fresh variables for all of the "fresh" vars
-- used in this phase and add them to the term substitution.
refreshTerms ::
  SharedContext {- ^ shared context -} ->
  StateSpec     {- ^ current phase spec -} ->
  OverrideMatcher arch md ()
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
-- an override's precondition are disjoint. Read-only allocations are
-- allowed to alias other read-only allocations, however.
enforceDisjointness ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  CrucibleContext arch -> W4.ProgramLoc -> StateSpec -> OverrideMatcher arch md ()
enforceDisjointness cc loc ss =
  do sym <- getSymInterface
     sub <- OM (use setupValueSub)
     let memsRW = Map.elems $ Map.intersectionWith (,) (view csAllocs ss) sub
         memsRO = Map.elems $ Map.intersectionWith (,) (view csConstAllocs ss) sub

     -- Ensure that all RW regions are disjoint from each other, and
     -- that all RW regions are disjoint from all RO regions.
     sequence_
        [ do c <- liftIO
                $ Crucible.buildDisjointRegionsAssertion
                    sym Crucible.PtrWidth
                    p (sz pty)
                    q (sz qty)
             addAssert c a

        | let dl = Crucible.llvmDataLayout (cc^.ccTypeCtx)

              sz p = W4.BVExpr
                       Crucible.PtrWidth
                       (Crucible.bytesToInteger (Crucible.memTypeSize dl p))
                       W4.initializationLoc

              a = Crucible.SimError loc $
                    Crucible.AssertFailureSimError "Memory regions not disjoint"
        , ((_ploc,pty),p):ps <- tails memsRW
        , ((_qloc,qty),q)    <- ps ++ memsRO
        ]

------------------------------------------------------------------------

-- | For each points-to statement read the memory value through the
-- given pointer (lhs) and match the value against the given pattern
-- (rhs).  Statements are processed in dependency order: a points-to
-- statement cannot be executed until bindings for any/all lhs
-- variables exist.
matchPointsTos :: forall arch md.
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options          {- ^ saw script print out opts -} ->
  SharedContext    {- ^ term construction context -} ->
  CrucibleContext arch {- ^ simulator context     -} ->
  CrucibleMethodSpecIR                               ->
  PrePost                                            ->
  [PointsTo]       {- ^ points-tos                -} ->
  OverrideMatcher arch md ()
matchPointsTos opts sc cc spec prepost = go False []
  where
    go ::
      Bool       {- progress indicator -} ->
      [PointsTo] {- delayed conditions -} ->
      [PointsTo] {- queued conditions  -} ->
      OverrideMatcher arch md ()

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
    checkPointsTo :: PointsTo -> OverrideMatcher arch md Bool
    checkPointsTo (PointsTo _loc p _) = checkSetupValue p

    checkSetupValue :: SetupValue -> OverrideMatcher arch md Bool
    checkSetupValue v =
      do m <- OM (use setupValueSub)
         return (all (`Map.member` m) (setupVars v))

    -- Compute the set of variable identifiers in a 'SetupValue'
    setupVars :: SetupValue -> Set AllocIndex
    setupVars v =
      case v of
        SetupVar    i            -> Set.singleton i
        SetupStruct xs           -> foldMap setupVars xs
        SetupArray  xs           -> foldMap setupVars xs
        SetupElem x _            -> setupVars x
        SetupField x _           -> setupVars x
        SetupTerm   _            -> Set.empty
        SetupNull                -> Set.empty
        SetupGlobal _            -> Set.empty
        SetupGlobalInitializer _ -> Set.empty


------------------------------------------------------------------------

computeReturnValue ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options               {- ^ saw script debug and print options     -} ->
  CrucibleContext arch  {- ^ context of the crucible simulation     -} ->
  SharedContext         {- ^ context for generating saw terms       -} ->
  CrucibleMethodSpecIR  {- ^ method specification                   -} ->
  Crucible.TypeRepr ret {- ^ representation of function return type -} ->
  Maybe SetupValue      {- ^ optional symbolic return value         -} ->
  OverrideMatcher arch md (Crucible.RegValue Sym ret)
                        {- ^ concrete return value                  -}

computeReturnValue _opts _cc _sc spec ty Nothing =
  case ty of
    Crucible.UnitRepr -> return ()
    _ -> failure (spec^.csLoc) BadReturnSpecification

computeReturnValue opts cc sc spec ty (Just val) =
  do (_memTy, Crucible.AnyValue xty xval) <- resolveSetupValue opts cc sc spec val
     case testEquality ty xty of
       Just Refl -> return xval
       Nothing -> failure (spec^.csLoc) BadReturnSpecification


------------------------------------------------------------------------

-- | Forget the type indexes and length of the arguments.
assignmentToList ::
  Ctx.Assignment (Crucible.RegEntry sym) ctx ->
  [Crucible.AnyValue sym]
assignmentToList = Ctx.toListFC (\(Crucible.RegEntry x y) -> Crucible.AnyValue x y)

------------------------------------------------------------------------

getSymInterface :: OverrideMatcher arch md Sym
getSymInterface = OM (use syminterface)

------------------------------------------------------------------------

-- | "Run" function for OverrideMatcher. The final result and state
-- are returned. The state will contain the updated globals and substitutions
runOverrideMatcher ::
   Sym                         {- ^ simulator                       -} ->
   Crucible.SymGlobalState Sym {- ^ initial global variables        -} ->
   Map AllocIndex (LLVMPtr (Crucible.ArchWidth arch)) {- ^ initial allocation substitution -} ->
   Map VarIndex Term           {- ^ initial term substitution       -} ->
   Set VarIndex                {- ^ initial free variables          -} ->
   W4.ProgramLoc               {- ^ override location information   -} ->
   OverrideMatcher arch md a   {- ^ matching action                 -} ->
   IO (Either OverrideFailure (a, OverrideState arch))
runOverrideMatcher sym g a t free loc (OM m) = runExceptT (runStateT m (initialState sym g a t free loc))

------------------------------------------------------------------------

-- | Assign the given pointer value to the given allocation index in
-- the current substitution. If there is already a binding for this
-- index, then add a pointer-equality constraint.
assignVar ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  AllocIndex      {- ^ variable index -} ->
  LLVMPtr (Crucible.ArchWidth arch) {- ^ concrete value -} ->
  OverrideMatcher arch md ()

assignVar cc loc var val =
  do old <- OM (setupValueSub . at var <<.= Just val)
     for_ old $ \val' ->
       do p <- liftIO (equalValsPred cc (Crucible.ptrToPtrVal val') (Crucible.ptrToPtrVal val))
          addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError "equality of aliased pointers"))

------------------------------------------------------------------------


assignTerm ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  CrucibleContext arch   {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                          ->
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher arch md ()

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
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  CrucibleContext arch {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                          ->
  Crucible.LLVMVal Sym
                     {- ^ concrete simulation value             -} ->
  Crucible.MemType   {- ^ expected memory type                  -} ->
  SetupValue         {- ^ expected specification value          -} ->
  OverrideMatcher arch md ()

matchArg sc cc loc prepost actual expectedTy expected@(SetupTerm expectedTT)
  | Cryptol.Forall [] [] tyexpr <- ttSchema expectedTT
  , Right tval <- Cryptol.evalType mempty tyexpr
  = do sym      <- getSymInterface
       let failMsg = StructuralMismatch actual expected expectedTy
       realTerm <- valueToSC sym loc failMsg tval actual
       matchTerm sc cc loc prepost realTerm (ttTerm expectedTT)

-- match the fields of struct point-wise
matchArg sc cc loc prepost (Crucible.LLVMValStruct xs) (Crucible.StructType fields) (SetupStruct zs) =
  sequence_
    [ matchArg sc cc loc prepost x y z
       | ((_,x),y,z) <- zip3 (V.toList xs)
                             (V.toList (Crucible.fiType <$> Crucible.siFields fields))
                             zs ]

matchArg _sc cc loc prepost actual@(Crucible.LLVMValInt blk off) expectedTy setupval =
  case setupval of
    SetupVar var | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
      do assignVar cc loc var (Crucible.LLVMPointer blk off)

    SetupNull | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
      do sym <- getSymInterface
         p   <- liftIO (Crucible.ptrIsNull sym Crucible.PtrWidth (Crucible.LLVMPointer blk off))
         addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError ("null-equality " ++ stateCond prepost)))

    SetupGlobal name | Just Refl <- testEquality (W4.bvWidth off) Crucible.PtrWidth ->
      do let mem = cc^.ccLLVMEmptyMem
         sym  <- getSymInterface
         Crucible.LLVMPointer blk' off' <- liftIO $ Crucible.doResolveGlobal sym mem (L.Symbol name)

         p1 <- liftIO (W4.natEq sym blk blk')
         p2 <- liftIO (W4.bvEq sym off off')
         p  <- liftIO (W4.andPred sym p1 p2)
         addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError ("global-equality " ++ stateCond prepost)))

    _ -> failure loc (StructuralMismatch actual setupval expectedTy)

matchArg _sc _cc loc _prepost actual expectedTy expected =
  failure loc (StructuralMismatch actual expected expectedTy)

------------------------------------------------------------------------

zeroValueSC :: SharedContext -> Crucible.Type -> IO Term
zeroValueSC sc tp = case Crucible.typeF tp of
  Crucible.Float -> fail "zeroValueSC: float unsupported"
  Crucible.Double -> fail "zeroValueSC: double unsupported"
  Crucible.Bitvector bs ->
    do n <- scNat sc (fromInteger (Crucible.bytesToBits bs))
       z <- scNat sc 0
       scBvNat sc n z
  Crucible.Array n tp' ->
    do sctp <- typeToSC sc tp'
       v <- zeroValueSC sc tp'
       scVector sc sctp (replicate (fromIntegral n) v)
  Crucible.Struct fs ->
    do tms <- mapM (zeroValueSC sc . view Crucible.fieldVal) (V.toList fs)
       scTuple sc tms

valueToSC ::
  Sym ->
  W4.ProgramLoc ->
  OverrideFailureReason ->
  Cryptol.TValue ->
  Crucible.LLVMVal Sym  ->
  OverrideMatcher arch md Term
valueToSC sym _loc _failMsg _ts (Crucible.LLVMValZero gtp)
  = liftIO $
     do sc <- (Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym))
        zeroValueSC sc gtp

valueToSC sym loc failMsg (Cryptol.TVTuple tys) (Crucible.LLVMValStruct vals)
  | length tys == length vals
  = do terms <- traverse (\(ty, tm) -> valueToSC sym loc failMsg ty (snd tm)) (zip tys (V.toList vals))
       sc    <- liftIO (Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym))
       liftIO $ scTuple sc terms

valueToSC sym loc failMsg (Cryptol.TVSeq _n Cryptol.TVBit) (Crucible.LLVMValInt base off) =
  do baseZero <- liftIO (W4.natEq sym base =<< W4.natLit sym 0)
     offTm    <- liftIO (Crucible.toSC sym off)
     case W4.asConstantPred baseZero of
       Just True  -> return offTm
       Just False -> failure loc failMsg
       _ -> do addAssert baseZero (Crucible.SimError loc (Crucible.GenericSimError "Expected bitvector value, but found pointer"))
               return offTm

-- This is a case for pointers, when we opaque types in Cryptol to represent them...
-- valueToSC sym _tval (Crucible.LLVMValInt base off) =
--   do base' <- Crucible.toSC sym base
--      off'  <- Crucible.toSC sym off
--      sc    <- Crucible.saw_ctx <$> readIORef (Crucible.sbStateManager sym)
--      Just <$> scTuple sc [base', off']

valueToSC sym loc failMsg (Cryptol.TVSeq n cryty) (Crucible.LLVMValArray ty vals)
  | toInteger (length vals) == n
  = do terms <- V.toList <$> traverse (valueToSC sym loc failMsg cryty) vals
       sc    <- liftIO (Crucible.saw_ctx <$> readIORef (W4.sbStateManager sym))
       t     <- liftIO (typeToSC sc ty)
       liftIO (scVector sc t terms)

valueToSC _ _ _ _ Crucible.LLVMValFloat{} =
  fail  "valueToSC: Real not supported"

valueToSC _sym loc failMsg _tval _val =
  failure loc failMsg

------------------------------------------------------------------------

typeToSC :: SharedContext -> Crucible.Type -> IO Term
typeToSC sc t =
  case Crucible.typeF t of
    Crucible.Bitvector sz -> scBitvector sc (fromInteger (Crucible.bytesToBits sz))
    Crucible.Float -> fail "typeToSC: float not supported"
    Crucible.Double -> fail "typeToSC: double not supported"
    Crucible.Array sz ty ->
      do n <- scNat sc (fromIntegral sz)
         ty' <- typeToSC sc ty
         scVecType sc n ty'
    Crucible.Struct fields ->
      do fields' <- V.toList <$> traverse (typeToSC sc . view Crucible.fieldVal) fields
         scTuple sc fields'

------------------------------------------------------------------------

matchTerm ::
  SharedContext   {- ^ context for constructing SAW terms    -} ->
  CrucibleContext arch {- ^ context for interacting with Crucible -} ->
  W4.ProgramLoc ->
  PrePost                                                       ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher arch md ()

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
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  CrucibleContext arch       ->
  CrucibleMethodSpecIR       ->
  PrePost                    ->
  SetupCondition             ->
  OverrideMatcher arch md ()
learnSetupCondition opts sc cc spec prepost (SetupCond_Equal loc val1 val2)  = learnEqual opts sc cc spec loc prepost val1 val2
learnSetupCondition _opts sc cc _    prepost (SetupCond_Pred loc tm)         = learnPred sc cc loc prepost (ttTerm tm)
learnSetupCondition _opts sc cc _    prepost (SetupCond_Ghost loc var val)   = learnGhost sc cc loc prepost var val


------------------------------------------------------------------------

learnGhost ::
  SharedContext                                          ->
  CrucibleContext arch                                   ->
  W4.ProgramLoc                                          ->
  PrePost                                                ->
  GhostGlobal                                            ->
  TypedTerm                                              ->
  OverrideMatcher arch md ()
learnGhost sc cc loc prepost var expected =
  do actual <- readGlobal var
     matchTerm sc cc loc prepost (ttTerm actual) (ttTerm expected)

------------------------------------------------------------------------

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
learnPointsTo ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  CrucibleContext arch       ->
  CrucibleMethodSpecIR       ->
  PrePost                    ->
  PointsTo                   ->
  OverrideMatcher arch md ()
learnPointsTo opts sc cc spec prepost (PointsTo loc ptr val) =
  do let tyenv = csAllocations spec
         nameEnv = csTypeNames spec
     memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv val
     (_memTy, ptr1) <- asPointer loc =<< resolveSetupValue opts cc sc spec ptr
     -- In case the types are different (from crucible_points_to_untyped)
     -- then the load type should be determined by the rhs.
     storTy <- Crucible.toStorableType memTy
     sym    <- getSymInterface

     mem    <- readGlobal $ Crucible.llvmMemVar
                          $ (cc^.ccLLVMContext)

     res  <- liftIO (Crucible.loadRawWithCondition sym mem ptr1 storTy)
     (p,r,v) <- case res of
                  Left e  -> failure loc (BadPointerLoad e)
                  Right x -> return x
     addAssert p (Crucible.SimError loc r)
     matchArg sc cc loc prepost v memTy val


------------------------------------------------------------------------

stateCond :: PrePost -> String
stateCond PreState = "precondition"
stateCond PostState = "postcondition"

-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options                                          ->
  SharedContext                                    ->
  CrucibleContext arch                             ->
  CrucibleMethodSpecIR                             ->
  W4.ProgramLoc                                    ->
  PrePost                                          ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher arch md ()
learnEqual opts sc cc spec loc prepost v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM opts cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM opts cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  let name = "equality " ++ stateCond prepost
  addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError name))

-- | Process a "crucible_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  CrucibleContext arch                                                ->
  W4.ProgramLoc                                                       ->
  PrePost                                                             ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher arch md ()
learnPred sc cc loc prepost t =
  do s <- OM (use termSub)
     u <- liftIO $ scInstantiateExt sc s t
     p <- liftIO $ resolveSAWPred cc u
     addAssert p (Crucible.SimError loc (Crucible.AssertFailureSimError (stateCond prepost)))

------------------------------------------------------------------------

-- | Perform an allocation as indicated by a 'crucible_alloc'
-- statement from the postcondition section.
executeAllocation ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                        ->
  CrucibleContext arch           ->
  (AllocIndex, (W4.ProgramLoc, Crucible.MemType)) ->
  OverrideMatcher arch RW ()
executeAllocation opts cc (var, (loc, memTy)) =
  do let sym = cc^.ccBackend
     let dl = Crucible.llvmDataLayout ?lc
     {-
     memTy <- case Crucible.asMemType symTy of
                Just memTy -> return memTy
                Nothing    -> fail "executAllocation: failed to resolve type"
                -}
     liftIO $ printOutLn opts Debug $ unwords ["executeAllocation:", show var, show memTy]
     let memVar = Crucible.llvmMemVar $ (cc^.ccLLVMContext)
     let w = Crucible.memTypeSize dl memTy
     mem <- readGlobal memVar
     sz <- liftIO $ W4.bvLit sym Crucible.PtrWidth (Crucible.bytesToInteger w)
     (ptr, mem') <- liftIO (Crucible.mallocRaw sym mem sz)
     writeGlobal memVar mem'
     assignVar cc loc var ptr

------------------------------------------------------------------------

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  CrucibleContext arch       ->
  CrucibleMethodSpecIR       ->
  SetupCondition             ->
  OverrideMatcher arch RW ()
executeSetupCondition opts sc cc spec (SetupCond_Equal _loc val1 val2) = executeEqual opts sc cc spec val1 val2
executeSetupCondition _opts sc cc _    (SetupCond_Pred _loc tm)        = executePred sc cc tm
executeSetupCondition _opts sc _  _    (SetupCond_Ghost _loc var val)  = executeGhost sc var val

------------------------------------------------------------------------

executeGhost ::
  SharedContext ->
  GhostGlobal ->
  TypedTerm ->
  OverrideMatcher arch RW ()
executeGhost sc var val =
  do s <- OM (use termSub)
     t <- liftIO (ttTermLens (scInstantiateExt sc s) val)
     writeGlobal var t

------------------------------------------------------------------------

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  Options                    ->
  SharedContext              ->
  CrucibleContext arch       ->
  CrucibleMethodSpecIR       ->
  PointsTo                   ->
  OverrideMatcher arch RW ()
executePointsTo opts sc cc spec (PointsTo loc ptr val) =
  do (_, ptr1) <- asPointer loc =<< resolveSetupValue opts cc sc spec ptr
     sym    <- getSymInterface

     -- In case the types are different (from crucible_points_to_untyped)
     -- then the load type should be determined by the rhs.
     (memTy1, Crucible.AnyValue vtp val1) <- resolveSetupValue opts cc sc spec val
     storTy <- Crucible.toStorableType memTy1

     let memVar = Crucible.llvmMemVar $ (cc^.ccLLVMContext)
     mem  <- readGlobal memVar
     mem' <- liftIO (Crucible.doStore sym mem ptr1 vtp storTy val1)
     writeGlobal memVar mem'


------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options                                          ->
  SharedContext                                    ->
  CrucibleContext arch                             ->
  CrucibleMethodSpecIR                             ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher arch md ()
executeEqual opts sc cc spec v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM opts cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM opts cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  addAssume p

-- | Process a "crucible_postcond" statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext     ->
  CrucibleContext arch ->
  TypedTerm        {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher arch md ()
executePred sc cc tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveSAWPred cc t
     addAssume p

------------------------------------------------------------------------

-- | Construct a completely symbolic pointer. This pointer could point to anything, or it could
-- be NULL.
executeFreshPointer ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  CrucibleContext arch {- ^ Crucible context       -} ->
  AllocIndex      {- ^ SetupVar allocation ID -} ->
  IO (LLVMPtr (Crucible.ArchWidth arch)) {- ^ Symbolic pointer value -}
executeFreshPointer cc (AllocIndex i) =
  do let mkName base = W4.systemSymbol (base ++ show i ++ "!")
         sym         = cc^.ccBackend
     blk <- W4.freshConstant sym (mkName "blk") W4.BaseNatRepr
     off <- W4.freshConstant sym (mkName "off") (W4.BaseBVRepr Crucible.PtrWidth)
     return (Crucible.LLVMPointer blk off)

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
    SetupVar _               -> return v
    SetupTerm tt             -> SetupTerm   <$> doTerm tt
    SetupStruct vs           -> SetupStruct <$> mapM (instantiateSetupValue sc s) vs
    SetupArray  vs           -> SetupArray  <$> mapM (instantiateSetupValue sc s) vs
    SetupElem _ _            -> return v
    SetupField _ _           -> return v
    SetupNull                -> return v
    SetupGlobal _            -> return v
    SetupGlobalInitializer _ -> return v
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

------------------------------------------------------------------------

resolveSetupValueLLVM ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options              ->
  CrucibleContext arch ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher arch md (Crucible.MemType, LLVMVal)
resolveSetupValueLLVM opts cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = csAllocations spec
         nameEnv = csTypeNames spec
     memTy <- liftIO $ typeOfSetupValue cc tyenv nameEnv sval
     sval' <- liftIO $ instantiateSetupValue sc s sval
     lval  <- liftIO $ resolveSetupVal cc m tyenv nameEnv sval' `X.catch` handleException opts
     return (memTy, lval)

resolveSetupValue ::
  Crucible.HasPtrWidth (Crucible.ArchWidth arch) =>
  Options              ->
  CrucibleContext arch ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher arch md (Crucible.MemType, Crucible.AnyValue Sym)
resolveSetupValue opts cc sc spec sval =
  do (memTy, lval) <- resolveSetupValueLLVM opts cc sc spec sval
     sym <- getSymInterface
     aval <- liftIO $ Crucible.unpackMemValue sym lval
     return (memTy, aval)

------------------------------------------------------------------------

asPointer ::
  (?lc :: Crucible.TypeContext, Crucible.HasPtrWidth (Crucible.ArchWidth arch)) =>
  W4.ProgramLoc ->
  (Crucible.MemType, Crucible.AnyValue Sym) ->
  OverrideMatcher arch md (Crucible.MemType, LLVMPtr (Crucible.ArchWidth arch))

asPointer
  _
  (Crucible.PtrType pty,
   Crucible.AnyValue Crucible.PtrRepr val)
  | Right pty' <- Crucible.asMemType pty
  = return (pty', val)

asPointer loc _ = failure loc BadPointerCast
