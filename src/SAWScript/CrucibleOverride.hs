{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}

module SAWScript.CrucibleOverride (methodSpecHandler, valueToSC) where

import           Control.Lens
import           Control.Exception
import           Control.Monad.Trans.State
import           Control.Monad.Trans.Except
import           Control.Monad.Trans.Class
import           Control.Monad.IO.Class
import           Control.Monad
import           Data.Either (partitionEithers)
import           Data.Foldable (for_, traverse_)
import           Data.List (tails)
import           Data.List.NonEmpty (NonEmpty(..))
import           Data.IORef (readIORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V

import qualified Data.Parameterized.Nonce as Nonce

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.CFG.Core as Crucible
                   (TypeRepr(UnitRepr), IntrinsicType, GlobalVar)
import qualified Lang.Crucible.Simulator.OverrideSim as Crucible
import qualified Lang.Crucible.Simulator.GlobalState as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible

import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.MemModel.Common as Crucible
import qualified Lang.Crucible.Solver.Interface as Crucible
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible
import qualified Lang.Crucible.Solver.SimpleBuilder as Crucible
import qualified Lang.Crucible.ProgramLoc as Crucible

import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NatRepr

import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Prelude (scEq)
import           Verifier.SAW.TypedAST

import           SAWScript.CrucibleMethodSpecIR
import           SAWScript.CrucibleResolveSetupValue
import           SAWScript.TypedTerm

-- | The 'OverrideMatcher' type provides the operations that are needed
-- to match a specification's arguments with the arguments provided by
-- the Crucible simulation in order to compute the variable substitution
-- and side-conditions needed to proceed.
newtype OverrideMatcher a
  = OM { unOM :: StateT OverrideState (ExceptT OverrideFailure IO) a }

data OverrideState = OverrideState
  { _setupValueSub :: Map AllocIndex (Crucible.RegValue Sym Crucible.LLVMPointerType)
  , _termSub       :: Map VarIndex Term
  , _asserts       :: [(Crucible.Pred Sym, Crucible.SimErrorReason)]
  , _assumes       :: [Crucible.Pred Sym]
  , _syminterface  :: Sym
  , _overrideGlobals :: Crucible.SymGlobalState Sym
  }

data OverrideFailure
  = BadSymType Crucible.SymType
  | AmbiguousPrecondition [PointsTo]
  | BadTermMatch Term Term -- ^ simulated and specified terms did not match
  | BadPointerCast -- ^ Pointer required to process points-to
  | BadReturnSpecification -- ^ type mismatch in return specification
  | NonlinearPatternNotSupported
  | BadPointerLoad String -- ^ loadRaw failed due to type error
  | StructuralMismatch (Crucible.LLVMVal Sym Crucible.PtrWidth)
                       SetupValue
                       Crucible.MemType
                        -- ^ simulated value, specified value, specified type
  deriving Show

instance Exception OverrideFailure

instance Functor     OverrideMatcher where fmap   = liftM
instance Applicative OverrideMatcher where pure x = OM (pure x)
                                           (<*>)  = ap
instance Monad       OverrideMatcher where return = pure
                                           m >>= f = OM (unOM . f =<< unOM m)
instance MonadIO     OverrideMatcher where liftIO io = OM (liftIO io)


makeLenses ''OverrideState

------------------------------------------------------------------------

-- | The initial override matching state starts with an empty substitution
-- and no assertions or assumptions.
initialState ::
  Sym ->
  Crucible.SymGlobalState Sym ->
  OverrideState
initialState = OverrideState Map.empty Map.empty [] []

------------------------------------------------------------------------

addAssert ::
  Crucible.Pred Sym       {- ^ property -} ->
  Crucible.SimErrorReason {- ^ reason   -} ->
  OverrideMatcher ()
addAssert p r = OM (asserts %= cons (p,r))

addAssume ::
  Crucible.Pred Sym       {- ^ property -} ->
  OverrideMatcher ()
addAssume p = OM (assumes %= cons p)

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
failure :: OverrideFailure -> OverrideMatcher a
failure e = OM (lift (throwE e))

------------------------------------------------------------------------

methodSpecHandler ::
  forall rtp args ret.
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext          {- ^ context for interacting with Crucible        -} ->
  [CrucibleMethodSpecIR]   {- ^ specification for current function override  -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  Crucible.OverrideSim Crucible.SAWCruciblePersonality Sym rtp args ret
     (Crucible.RegValue Sym ret)
methodSpecHandler sc cc css retTy = do
  let L.Symbol fsym = csName (head css)
  liftIO $ putStrLn $ "Executing override for `" ++ fsym ++ "`"
  Crucible.RegMap args <- Crucible.getOverrideArgs
  globals <- Crucible.readGlobals
  sym     <- Crucible.getSymInterface

  gs <- liftIO (buildGlobalsList sym (length css) globals)

  matches
     <- liftIO $
        zipWithM (\g cs -> runOverrideMatcher sym g
                             (methodSpecHandler1 sc cc args retTy cs)) gs css

  outputs <- case partitionEithers matches of
               (e,[]  ) -> fail ("All overrides failed: " ++ show e)
               (_,s:ss) -> return (s:|ss)

  Crucible.writeGlobals =<< liftIO (muxGlobal sym (fmap snd outputs))

  liftIO $
    do -- assert the disjunction of all the preconditions
       do ps <- traverse (conjunction sym . toListOf (_2 . asserts . folded . _1)) outputs
          p  <- disjunction sym ps
          Crucible.sbAddAssertion (ccBackend cc) p
            (Crucible.AssertFailureSimError ("No applicable override for " ++ fsym))

       -- Postcondition can be used if precondition holds
       for_ outputs $ \(_,output) ->
         do p       <- conjunction sym (toListOf (asserts . folded . _1) output)
            q       <- conjunction sym (view assumes output)
            p_imp_q <- Crucible.impliesPred sym p q
            Crucible.sbAddAssumption (ccBackend cc) p_imp_q

       muxReturnValue sym retTy outputs

-- | When two global states are merged, only the writes since the last branch
-- are actually merged. Therefore we need to add enough branches to the global
-- states so that as we merge all of the results of applying overrides that there
-- are enough branches left over at the end to mux.
buildGlobalsList :: Sym -> Int -> Crucible.SymGlobalState Sym ->
  IO [Crucible.SymGlobalState Sym]
buildGlobalsList _   1 g = return [g]
buildGlobalsList sym n g =
  do g1 <- Crucible.globalPushBranch sym intrinsics g
     gs <- buildGlobalsList sym (n-1) g1
     return (g1:gs)

-- | Compute the conjunction of a set of predicates.
conjunction :: Foldable t => Sym -> t (Crucible.Pred Sym) -> IO (Crucible.Pred Sym)
conjunction sym = foldM (Crucible.andPred sym) (Crucible.truePred sym)

-- | Compute the disjunction of a set of predicates.
disjunction :: Foldable t => Sym -> t (Crucible.Pred Sym) -> IO (Crucible.Pred Sym)
disjunction sym = foldM (Crucible.orPred sym) (Crucible.falsePred sym)

-- | Compute the return value from a list of structurally matched
-- overrides. The result will be a muxed value guarded by the
-- preconditions of each of the overrides.
muxReturnValue ::
  Sym                   {- ^ symbolic simulator parameters -} ->
  Crucible.TypeRepr ret {- ^ type of return value          -} ->
  NonEmpty (Crucible.RegValue Sym ret, OverrideState)
                        {- ^ possible overrides            -} ->
  IO (Crucible.RegValue Sym ret) {- ^ muxed return value   -}
muxReturnValue _   _     ((val,_):|[]) = return val
muxReturnValue sym retTy ((val,x):|y:z) =
  do ys   <- muxReturnValue sym retTy (y:|z)
     here <- conjunction sym (map fst (view asserts x))
     Crucible.muxRegForType sym intrinsics retTy here val ys

muxGlobal :: Sym -> NonEmpty OverrideState -> IO (Crucible.SymGlobalState Sym)
muxGlobal _ (x:|[]) = return (view overrideGlobals x)
muxGlobal sym (x:|y:z) =
  do ys   <- muxGlobal sym (y:|z)
     here <- conjunction sym (toListOf (asserts . folded . _1) x)
     globalMuxUnleveled sym here (view overrideGlobals x) ys

-- | This mux function can handle cases wher the right-hand side has
-- more branches that the left-hand side. This can happen when an
-- override specification was aborted due to structural mismatch.
globalMuxUnleveled ::
  Sym -> Crucible.MuxFn (Crucible.Pred Sym) (Crucible.SymGlobalState Sym)
globalMuxUnleveled sym p l r
  | Crucible._globalPendingBranches l < Crucible._globalPendingBranches r =
     do r' <- Crucible.globalAbortBranch sym intrinsics r
        globalMuxUnleveled sym p l r'
  | otherwise = Crucible.globalMuxFn sym intrinsics p l r

------------------------------------------------------------------------

methodSpecHandler1 ::
  forall ret ctx.
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext          {- ^ context for interacting with Crucible        -} ->
  Ctx.Assignment (Crucible.RegEntry Sym) ctx
           {- ^ type representation of function return value -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  OverrideMatcher (Crucible.RegValue Sym ret)
methodSpecHandler1 sc cc args retTy cs =
    do args' <- (traverse . _1) resolveMemType (Map.elems (csArgBindings cs))

       sym <- getSymInterface

       let aux memTy (Crucible.AnyValue tyrep val) =
             do storTy <- Crucible.toStorableType memTy
                Crucible.packMemValue sym storTy tyrep val

       xs <- liftIO (zipWithM aux (map fst args') (assignmentToList args))

       -- todo: fail if list lengths mismatch
       sequence_ [ matchArg sc cc x y z | (x,(y,z)) <- zip xs args' ]
       processPrePointsTos sc cc cs (csPrePointsTos cs)
       traverse_ (learnSetupCondition sc cc cs) (csPreconditions cs)
       enforceDisjointness cc cs
       traverse_ (executePostAllocation cc) (Map.assocs (csPostAllocations cs))
       traverse_ (executePointsTo sc cc cs) (csPostPointsTos cs)
       traverse_ (executeSetupCondition sc cc cs) (csPostconditions cs)
       computeReturnValue cc sc cs retTy (csRetValue cs)

------------------------------------------------------------------------

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint.
enforceDisjointness :: CrucibleContext -> CrucibleMethodSpecIR -> OverrideMatcher ()
enforceDisjointness cc spec =
  do sym <- getSymInterface
     sub <- OM (use setupValueSub)
     let m = Map.elems $ Map.intersectionWith (,) (csAllocations spec) sub

     let dl = TyCtx.llvmDataLayout (Crucible.llvmTypeCtx (ccLLVMContext cc))

         sz p = Crucible.BVElt
                  Crucible.ptrWidth
                  (fromIntegral (Crucible.memTypeSize dl p))
                  Crucible.initializationLoc

     liftIO $ sequence_
        [ Crucible.assertDisjointRegions'
            "enforcing disjoint allocations"
            sym Crucible.ptrWidth
            p (sz pty)
            q (sz qty)
        | (pty,p):ps <- tails m
        , (qty,q)    <- ps
        ]

------------------------------------------------------------------------

-- | For each points-to statement from the precondition section of an
-- override spec, read the memory value through the given pointer
-- (lhs) and match the value against the given pattern (rhs).
-- Statements are processed in dependency order: a points-to statement
-- cannot be executed until bindings for any/all lhs variables exist.
processPrePointsTos ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext    {- ^ term construction context -} ->
  CrucibleContext  {- ^ simulator context         -} ->
  CrucibleMethodSpecIR                               ->
  [PointsTo]       {- ^ points-to preconditions   -} ->
  OverrideMatcher ()
processPrePointsTos sc cc spec = go False []
  where
    go ::
      Bool       {- progress indicator -} ->
      [PointsTo] {- delayed conditions -} ->
      [PointsTo] {- queued conditions  -} ->
      OverrideMatcher ()

    -- all conditions processed, success
    go _ [] [] = return ()

    -- not all conditions processed, no progress, failure
    go False delayed [] = failure (AmbiguousPrecondition delayed)

    -- not all conditions processed, progress made, resume delayed conditions
    go True delayed [] = go False [] delayed

    -- progress the next points-to in the work queue
    go progress delayed (c:cs) =
      do ready <- checkPointsTo c
         if ready then
           do learnPointsTo sc cc spec c
              go True delayed cs
         else
           do go progress (c:delayed) cs

    -- determine if a precondition is ready to be checked
    checkPointsTo :: PointsTo -> OverrideMatcher Bool
    checkPointsTo (PointsTo p _) = checkSetupValue p

    checkSetupValue :: SetupValue -> OverrideMatcher Bool
    checkSetupValue v =
      do m <- OM (use setupValueSub)
         return (all (`Map.member` m) (setupVars v))

    -- Compute the set of variable identifiers in a 'SetupValue'
    setupVars :: SetupValue -> Set AllocIndex
    setupVars v =
      case v of
        SetupVar    i  -> Set.singleton i
        SetupStruct xs -> foldMap setupVars xs
        SetupArray  xs -> foldMap setupVars xs
        SetupElem x _  -> setupVars x
        SetupTerm   _  -> Set.empty
        SetupNull      -> Set.empty
        SetupGlobal _  -> Set.empty


------------------------------------------------------------------------

-- | Compute the 'Crucible.MemType' for a given 'Crucible.SymType' or throw
-- an error.
resolveMemType ::
  (?lc :: TyCtx.LLVMContext) =>
  Crucible.SymType           ->
  OverrideMatcher Crucible.MemType
resolveMemType ty =
  case TyCtx.asMemType ty of
    Nothing    -> failure (BadSymType ty)
    Just memTy -> return memTy

------------------------------------------------------------------------

computeReturnValue ::
  (?lc :: TyCtx.LLVMContext) =>
  CrucibleContext       {- ^ context of the crucible simulation     -} ->
  SharedContext         {- ^ context for generating saw terms       -} ->
  CrucibleMethodSpecIR  {- ^ method specification                   -} ->
  Crucible.TypeRepr ret {- ^ representation of function return type -} ->
  Maybe SetupValue      {- ^ optional symbolic return value         -} ->
  OverrideMatcher (Crucible.RegValue Sym ret)
                        {- ^ concrete return value                  -}

computeReturnValue _ _ _ ty Nothing =
  case ty of
    Crucible.UnitRepr -> return ()
    _ -> failure BadReturnSpecification

computeReturnValue cc sc spec ty (Just val) =
  do (_memTy, Crucible.AnyValue xty xval) <- resolveSetupValue cc sc spec val
     case NatRepr.testEquality ty xty of
       Just NatRepr.Refl -> return xval
       Nothing -> failure BadReturnSpecification


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

-- | "Run" function for OverrideMatcher.
runOverrideMatcher ::
   Sym ->
   Crucible.SymGlobalState Sym ->
   OverrideMatcher a ->
   IO (Either OverrideFailure (a, OverrideState))
runOverrideMatcher sym g (OM m) = runExceptT (runStateT m (initialState sym g))

------------------------------------------------------------------------

-- | Assign the given pointer value to the given allocation index in
-- the current substitution. If there is already a binding for this
-- index, then add a pointer-equality constraint.
assignVar ::
  CrucibleContext         {- ^ context for interacting with Crucible -} ->
  AllocIndex                                     {- ^ variable index -} ->
  Crucible.RegValue Sym Crucible.LLVMPointerType {- ^ concrete value -} ->
  OverrideMatcher ()

assignVar cc var val =
  do old <- OM (setupValueSub . at var <<.= Just val)
     for_ old $ \val' ->
       do p <- liftIO (equalValsPred cc (packPointer val') (packPointer val))
          addAssert p (Crucible.AssertFailureSimError "equality of aliased pointers")

------------------------------------------------------------------------


assignTerm ::
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher ()

assignTerm var val =
  do old <- OM (termSub . at var <<.= Just val)
     for_ old $ \_ ->
       failure NonlinearPatternNotSupported


------------------------------------------------------------------------

matchArg ::
  SharedContext      {- ^ context for constructing SAW terms    -} ->
  CrucibleContext    {- ^ context for interacting with Crucible -} ->
  Crucible.LLVMVal Sym Crucible.PtrWidth
                     {- ^ concrete simulation value             -} ->
  Crucible.MemType   {- ^ expected memory type                  -} ->
  SetupValue         {- ^ expected specification value          -} ->
  OverrideMatcher ()

matchArg _sc cc (Crucible.LLVMValPtr blk end off) _memTy (SetupVar var) =
  assignVar cc var (unpackPointer (Crucible.LLVMPtr blk end off))

-- match the fields of struct point-wise
matchArg sc cc (Crucible.LLVMValStruct xs) (Crucible.StructType fields) (SetupStruct zs) =
  sequence_
    [ matchArg sc cc x y z
       | ((_,x),y,z) <- zip3 (V.toList xs) (V.toList (Crucible.fiType <$> Crucible.siFields fields)) zs ]

matchArg sc cc realVal _ (SetupTerm expected) =
  do sym      <- getSymInterface
     realTerm <- liftIO (valueToSC sym realVal)
     matchTerm sc cc realTerm (ttTerm expected)

matchArg _sc _cc (Crucible.LLVMValPtr blk end off) _ SetupNull =
  do sym <- getSymInterface
     let ptr = Crucible.LLVMPtr blk end off
     p <- liftIO (Crucible.isNullPointer sym (unpackPointer ptr))
     addAssert p (Crucible.AssertFailureSimError "null-equality precondition")

matchArg _sc cc (Crucible.LLVMValPtr blk1 _ off1) _ (SetupGlobal name) =
  do sym <- getSymInterface
     let mem = ccEmptyMemImpl cc
     ptr2 <- liftIO $ Crucible.doResolveGlobal sym mem (L.Symbol name)
     let (Crucible.LLVMPtr blk2 _ off2) = packPointer' ptr2
     p1 <- liftIO (Crucible.natEq sym blk1 blk2)
     p2 <- liftIO (Crucible.bvEq sym off1 off2)
     p  <- liftIO (Crucible.andPred sym p1 p2)
     addAssert p (Crucible.AssertFailureSimError "global-equality precondition")

matchArg _sc _cc actual expectedTy expected =
  failure (StructuralMismatch actual expected expectedTy)

------------------------------------------------------------------------

-- TODO: this seems general enough that it could go in the Crucible
-- SAWCore backend
valueToSC ::
  Crucible.SAWCoreBackend Nonce.GlobalNonceGenerator ->
  Crucible.LLVMVal Sym Crucible.PtrWidth ->
  IO Term

valueToSC sym (Crucible.LLVMValInt _ bv) =
  Crucible.toSC sym bv

valueToSC sym (Crucible.LLVMValStruct vals) =
  do terms <- V.toList <$> traverse (valueToSC sym . snd) vals
     sc    <- Crucible.saw_ctx <$> readIORef (Crucible.sbStateManager sym)
     scTuple sc terms

valueToSC sym (Crucible.LLVMValPtr base sz off) =
  do base' <- Crucible.toSC sym base
     sz'   <- Crucible.toSC sym sz
     off'  <- Crucible.toSC sym off
     sc    <- Crucible.saw_ctx <$> readIORef (Crucible.sbStateManager sym)
     scTuple sc [base', sz', off']

valueToSC sym (Crucible.LLVMValArray ty vals) =
  do terms <- V.toList <$> traverse (valueToSC sym) vals
     sc    <- Crucible.saw_ctx <$> readIORef (Crucible.sbStateManager sym)
     t     <- typeToSC sc ty
     scVector sc t terms

valueToSC _ Crucible.LLVMValReal{} =
  fail "valueToSC: Real not supported"

------------------------------------------------------------------------

typeToSC :: SharedContext -> Crucible.Type -> IO Term
typeToSC sc t =
  case Crucible.typeF t of
    Crucible.Bitvector sz -> scBitvector sc (fromIntegral sz)
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
  CrucibleContext {- ^ context for interacting with Crucible -} ->
  Term            {- ^ exported concrete term                -} ->
  Term            {- ^ expected specification term           -} ->
  OverrideMatcher ()

matchTerm _ _ real expect | real == expect = return ()
matchTerm sc cc real expect =
  case unwrapTermF expect of
    FTermF (ExtCns ec) -> assignTerm (ecVarIndex ec) real

    -- test whether the pattern is a concrete term
    _ | Set.null (getAllExtSet expect) ->
      do t <- liftIO $ scEq sc real expect
         p <- liftIO $ resolveSAWPred cc t
         addAssert p (Crucible.AssertFailureSimError "literal equality precondition")

    _ -> failure (BadTermMatch real expect)

------------------------------------------------------------------------

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
learnSetupCondition ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  SetupCondition             ->
  OverrideMatcher ()
learnSetupCondition sc cc spec (SetupCond_Equal val1 val2)  = learnEqual sc cc spec val1 val2
learnSetupCondition sc cc _    (SetupCond_Pred tm)          = learnPred sc cc (ttTerm tm)
learnSetupCondition sc cc _    (SetupCond_Ghost var val)    = learnGhost sc cc var val


------------------------------------------------------------------------

learnGhost ::
  SharedContext                                          ->
  CrucibleContext                                        ->
  Crucible.GlobalVar (Crucible.IntrinsicType GhostValue) ->
  TypedTerm                                              ->
  OverrideMatcher ()
learnGhost sc cc var expected =
  do actual <- readGlobal var
     matchTerm sc cc (ttTerm actual) (ttTerm expected)

------------------------------------------------------------------------

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
learnPointsTo ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  PointsTo                   ->
  OverrideMatcher ()
learnPointsTo sc cc spec (PointsTo ptr val) =
  do let tyenv = Map.union (csAllocations spec) (csFreshPointers spec)
     memTy <- liftIO $ typeOfSetupValue cc tyenv val
     (_memTy, ptr1) <- asPointer =<< resolveSetupValue cc sc spec ptr
     -- In case the types are different (from crucible_points_to_untyped)
     -- then the load type should be determined by the rhs.
     storTy <- Crucible.toStorableType memTy
     sym    <- getSymInterface

     mem    <- readGlobal $ Crucible.llvmMemVar
                          $ Crucible.memModelOps
                          $ ccLLVMContext cc

     res  <- liftIO (Crucible.loadRawWithCondition sym mem (packPointer' ptr1) storTy)
     (p,r,v) <- case res of
                  Left e  -> failure (BadPointerLoad e)
                  Right x -> return x
     addAssert p r
     matchArg sc cc v memTy val


------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  SharedContext                                    ->
  CrucibleContext                                  ->
  CrucibleMethodSpecIR                             ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher ()
learnEqual sc cc spec v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  addAssert p (Crucible.AssertFailureSimError "equality precondition")

-- | Process a "crucible_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  CrucibleContext                                                     ->
  Term             {- ^ the precondition to learn                  -} ->
  OverrideMatcher ()
learnPred sc cc t =
  do s <- OM (use termSub)
     u <- liftIO $ scInstantiateExt sc s t
     p <- liftIO $ resolveSAWPred cc u
     addAssert p (Crucible.AssertFailureSimError "precondition")

------------------------------------------------------------------------

-- | Perform an allocation as indicated by a 'crucible_alloc'
-- statement from the postcondition section.
executePostAllocation ::
  (?lc :: TyCtx.LLVMContext) =>
  CrucibleContext            ->
  (AllocIndex, Crucible.MemType)      ->
  OverrideMatcher ()
executePostAllocation cc (var, memTy) =
  do let sym = ccBackend cc
     let dl = TyCtx.llvmDataLayout ?lc
     liftIO $ putStrLn $ unwords ["executePostAllocation:", show var, show memTy]
     let memVar = Crucible.llvmMemVar $ Crucible.memModelOps $ ccLLVMContext cc
     let w = Crucible.memTypeSize dl memTy
     mem <- readGlobal memVar
     sz <- liftIO $ Crucible.bvLit sym Crucible.ptrWidth (fromIntegral w)
     (ptr, mem') <- liftIO (Crucible.doMalloc sym mem sz)
     writeGlobal memVar mem'
     assignVar cc var ptr

------------------------------------------------------------------------

-- | Update the simulator state based on the postconditions from the
-- procedure specification.
executeSetupCondition ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  SetupCondition             ->
  OverrideMatcher ()
executeSetupCondition sc cc spec (SetupCond_Equal val1 val2) = executeEqual sc cc spec val1 val2
executeSetupCondition sc cc _    (SetupCond_Pred tm)         = executePred sc cc tm
executeSetupCondition sc _  _    (SetupCond_Ghost var val)   = executeGhost sc var val

------------------------------------------------------------------------

executeGhost ::
  SharedContext ->
  Crucible.GlobalVar (Crucible.IntrinsicType GhostValue) ->
  TypedTerm ->
  OverrideMatcher ()
executeGhost sc var val =
  do s <- OM (use termSub)
     t <- liftIO (ttTermLens (scInstantiateExt sc s) val)
     writeGlobal var t

------------------------------------------------------------------------

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  PointsTo                   ->
  OverrideMatcher ()
executePointsTo sc cc spec (PointsTo ptr val) =
  do (_, ptr1) <- asPointer =<< resolveSetupValue cc sc spec ptr
     sym    <- getSymInterface

     -- In case the types are different (from crucible_points_to_untyped)
     -- then the load type should be determined by the rhs.
     (memTy1, val1) <- resolveSetupValue cc sc spec val
     storTy <- Crucible.toStorableType memTy1

     let memVar = Crucible.llvmMemVar $ Crucible.memModelOps $ ccLLVMContext cc
     mem  <- readGlobal memVar
     mem' <- liftIO (Crucible.doStore sym mem ptr1 storTy val1)
     writeGlobal memVar mem'


------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the postcondition
-- section of the CrucibleSetup block.
executeEqual ::
  SharedContext                                    ->
  CrucibleContext                                  ->
  CrucibleMethodSpecIR                             ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher ()
executeEqual sc cc spec v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM cc sc spec v2
  p         <- liftIO (equalValsPred cc val1 val2)
  addAssume p

-- | Process a "crucible_postcond" statement from the postcondition
-- section of the CrucibleSetup block.
executePred ::
  SharedContext     ->
  CrucibleContext                                  ->
  TypedTerm        {- ^ the term to assert as a postcondition -} ->
  OverrideMatcher ()
executePred sc cc tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveSAWPred cc t
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
    SetupStruct vs -> SetupStruct <$> mapM (instantiateSetupValue sc s) vs
    SetupArray  vs -> SetupArray <$> mapM (instantiateSetupValue sc s) vs
    SetupElem _ _  -> return v
    SetupNull      -> return v
    SetupGlobal _  -> return v
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

------------------------------------------------------------------------

resolveSetupValueLLVM ::
  CrucibleContext      ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher (Crucible.MemType, LLVMVal)
resolveSetupValueLLVM cc sc spec sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let tyenv = Map.union (csAllocations spec) (csFreshPointers spec)
     memTy <- liftIO $ typeOfSetupValue cc tyenv sval
     sval' <- liftIO $ instantiateSetupValue sc s sval
     let env = fmap packPointer m
     lval <- liftIO $ resolveSetupVal cc env tyenv sval'
     return (memTy, lval)

resolveSetupValue ::
  CrucibleContext      ->
  SharedContext        ->
  CrucibleMethodSpecIR ->
  SetupValue           ->
  OverrideMatcher (Crucible.MemType, Crucible.AnyValue Sym)
resolveSetupValue cc sc spec sval =
  do (memTy, lval) <- resolveSetupValueLLVM cc sc spec sval
     sym <- getSymInterface
     aval <- liftIO $ Crucible.unpackMemValue sym lval
     return (memTy, aval)

packPointer' ::
  Crucible.RegValue Sym Crucible.LLVMPointerType ->
  Crucible.LLVMPtr Sym Crucible.PtrWidth
packPointer' (Crucible.RolledType xs) = Crucible.LLVMPtr blk end off
  where
    Crucible.RV blk = xs^._1
    Crucible.RV end = xs^._2
    Crucible.RV off = xs^._3

unpackPointer ::
  Crucible.LLVMPtr Sym Crucible.PtrWidth ->
  Crucible.RegValue Sym Crucible.LLVMPointerType
unpackPointer (Crucible.LLVMPtr blk end off) =
  Crucible.RolledType
  (Ctx.empty Ctx.%> Crucible.RV blk Ctx.%> Crucible.RV end Ctx.%> Crucible.RV off)

------------------------------------------------------------------------

asPointer ::
  (?lc :: TyCtx.LLVMContext) =>
  (Crucible.MemType, Crucible.AnyValue Sym) ->
  OverrideMatcher (Crucible.MemType, Crucible.RegValue Sym Crucible.LLVMPointerType)

asPointer
  (Crucible.PtrType pty,
   Crucible.AnyValue Crucible.LLVMPointerRepr val)
  | Just pty' <- TyCtx.asMemType pty
  = return (pty', val)

asPointer _ = failure BadPointerCast
