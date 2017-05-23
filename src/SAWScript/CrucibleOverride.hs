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
import           Control.Monad.State
import           Data.Foldable (traverse_)
import           Data.List (tails)
import           Data.IORef (readIORef)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V

import qualified Data.Parameterized.Nonce as Nonce

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.Core as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim as Crucible
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
import           Verifier.SAW.TypedAST

import           SAWScript.Builtins
import           SAWScript.CrucibleMethodSpecIR
import           SAWScript.CrucibleResolveSetupValue
import           SAWScript.TypedTerm

-- | The 'OverrideMatcher' type provides the operations that are needed
-- to match a specification's arguments with the arguments provided by
-- the Crucible simulation in order to compute the variable substitution
-- and side-conditions needed to proceed.
newtype OverrideMatcher a
  = OM { unOM :: forall rtp l ret.
        StateT
          OverrideState
          (Crucible.OverrideSim Crucible.SAWCruciblePersonality Sym rtp l ret)
          a }

data OverrideState = OverrideState
  { _setupValueSub :: Map AllocIndex (Crucible.RegValue Sym Crucible.LLVMPointerType)
  , _termSub       :: Map VarIndex Term
  }

data OverrideFailure
  = BadSymType Crucible.SymType
  | AmbiguousPrecondition [PointsTo]
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
initialState :: OverrideState
initialState = OverrideState Map.empty Map.empty

------------------------------------------------------------------------

-- | Abort the current computation by raising the given 'OverrideFailure'
-- exception.
failure :: OverrideFailure -> OverrideMatcher a
failure e = OM (liftIO (throwIO e))

------------------------------------------------------------------------

methodSpecHandler ::
  forall rtp args ret.
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext            {- ^ context for constructing SAW terms           -} ->
  CrucibleContext          {- ^ context for interacting with Crucible        -} ->
  CrucibleMethodSpecIR     {- ^ specification for current function override  -} ->
  Crucible.TypeRepr ret    {- ^ type representation of function return value -} ->
  Crucible.OverrideSim Crucible.SAWCruciblePersonality Sym rtp args ret (Crucible.RegValue Sym ret)
methodSpecHandler sc cc cs retTy = do
  let L.Symbol fsym = csName cs
  liftIO $ putStrLn $ "Executing override for `" ++ fsym ++ "`"

  Crucible.RegMap args <- Crucible.getOverrideArgs
  runOverrideMatcher $
    do args' <- (traverse . _1) resolveMemType (Map.elems (csArgBindings cs))

       sym <- liftSim Crucible.getSymInterface

       let aux memTy (Crucible.AnyValue tyrep val) =
             do storTy <- Crucible.toStorableType memTy
                Crucible.packMemValue sym storTy tyrep val

       xs <- liftIO (zipWithM aux (map fst args') (assignmentToList args))

       -- todo: fail if list lengths mismatch
       sequence_ [ matchArg cc x y z | (x,(y,z)) <- zip xs args' ]
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
  do sym <- liftSim Crucible.getSymInterface
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
    _ -> fail "computeReturnValue: missing crucible_return specification"

computeReturnValue cc sc spec ty (Just val) =
  do (_memTy, Crucible.AnyValue xty xval) <- resolveSetupValue cc sc spec val
     case NatRepr.testEquality ty xty of
       Just NatRepr.Refl -> return xval
       Nothing -> fail "computeReturnValue: Unexpected return type"


------------------------------------------------------------------------

-- | Forget the type indexes and length of the arguments.
assignmentToList ::
  Ctx.Assignment (Crucible.RegEntry sym) ctx ->
  [Crucible.AnyValue sym]
assignmentToList = Ctx.toListFC (\(Crucible.RegEntry x y) -> Crucible.AnyValue x y)

------------------------------------------------------------------------

liftSim :: (forall rtp l ret. Crucible.OverrideSim Crucible.SAWCruciblePersonality Sym rtp l ret a) -> OverrideMatcher a
liftSim m = OM (lift m)

------------------------------------------------------------------------

-- | "Run" function for OverrideMatcher.
runOverrideMatcher ::
  OverrideMatcher a ->
  Crucible.OverrideSim Crucible.SAWCruciblePersonality Sym rtp l r a
runOverrideMatcher (OM m) = evalStateT m initialState

------------------------------------------------------------------------

assignVar ::
  AllocIndex                                     {- ^ variable index -} ->
  Crucible.RegValue Sym Crucible.LLVMPointerType {- ^ concrete value -} ->
  OverrideMatcher ()

assignVar var val =
  OM $ zoom (setupValueSub . at var) $

  do old <- get
     case old of
       Nothing -> put (Just val)
       Just _ -> fail "Unifying multiple occurrences of variables not yet supported"

------------------------------------------------------------------------


assignTerm ::
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher ()

assignTerm var val =
  OM $ zoom (termSub . at var) $

  do old <- get
     case old of
       Nothing -> put (Just val)
       Just _  -> fail "Unifying multiple occurrences of variables not yet supported"


------------------------------------------------------------------------

matchArg ::
  CrucibleContext                                                             ->
  Crucible.LLVMVal Sym Crucible.PtrWidth {- ^ concrete simulation value    -} ->
  Crucible.MemType                       {- ^ expected memory type         -} ->
  SetupValue                             {- ^ expected specification value -} ->
  OverrideMatcher ()

matchArg _cc (Crucible.LLVMValPtr blk end off) _memTy (SetupVar var) =
  assignVar var (unpackPointer (Crucible.LLVMPtr blk end off))

-- match the fields of struct point-wise
matchArg cc (Crucible.LLVMValStruct xs) (Crucible.StructType fields) (SetupStruct zs) =
  sequence_
    [ matchArg cc x y z
       | ((_,x),y,z) <- zip3 (V.toList xs) (V.toList (Crucible.fiType <$> Crucible.siFields fields)) zs ]

matchArg
  _cc
  realVal _
  (SetupTerm (TypedTerm _expectedTermTy expectedTerm)) =

  do sym      <- liftSim Crucible.getSymInterface
     realTerm <- liftIO (valueToSC sym realVal)
     matchTerm realTerm expectedTerm

matchArg cc (Crucible.LLVMValPtr blk end off) _ SetupNull =
  do sym <- liftSim Crucible.getSymInterface
     let ptr = Crucible.LLVMPtr blk end off
     p <- liftIO $ Crucible.isNullPointer sym (unpackPointer ptr)
     let err = Crucible.AssertFailureSimError "null-equality precondition"
     liftIO $ Crucible.sbAddAssertion (ccBackend cc) p err

matchArg cc (Crucible.LLVMValPtr blk1 _ off1) _ (SetupGlobal name) =
  do sym <- liftSim Crucible.getSymInterface
     let mem = ccEmptyMemImpl cc
     ptr2 <- liftIO $ Crucible.doResolveGlobal sym mem (L.Symbol name)
     let (Crucible.LLVMPtr blk2 _ off2) = packPointer' ptr2
     p1 <- liftIO $ Crucible.natEq sym blk1 blk2
     p2 <- liftIO $ Crucible.bvEq sym off1 off2
     p <- liftIO $ Crucible.andPred sym p1 p2
     let err = Crucible.AssertFailureSimError "global-equality precondition"
     liftIO $ Crucible.sbAddAssertion (ccBackend cc) p err

matchArg _cc actual expectedTy expected =
  fail $ "Argument mismatch: " ++
          show actual ++ ", " ++
          show expected ++ " : " ++ show expectedTy

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
  Term {- ^ exported concrete term      -} ->
  Term {- ^ expected specification term -} ->
  OverrideMatcher ()

matchTerm real expect | real == expect = return ()
matchTerm real expect =
  case (unwrapTermF real, unwrapTermF expect) of
    (_, FTermF (ExtCns ec)) -> assignTerm (ecVarIndex ec) real
    _                       -> fail $ "matchTerm: Unable to match (" ++ show real ++
                               ") with (" ++ show expect ++ ")"

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
learnSetupCondition sc cc _    (SetupCond_Pred tm)          = learnPred sc cc tm


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
  do liftIO $ putStrLn $ "Checking points to: " ++
                         show ptr ++ " -> " ++ show val
     (memTy,ptr1) <- asPointer =<< resolveSetupValue cc sc spec ptr
     storTy <- Crucible.toStorableType memTy
     sym    <- liftSim Crucible.getSymInterface

     mem    <- liftSim
             $ Crucible.readGlobal $ Crucible.llvmMemVar
             $ Crucible.memModelOps $ ccLLVMContext cc

     v      <- liftIO (Crucible.loadRaw sym mem (packPointer' ptr1) storTy)
     matchArg cc v memTy val


------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  SharedContext                                                       ->
  CrucibleContext                                                     ->
  CrucibleMethodSpecIR                                                ->
  SetupValue       {- ^ first value to compare                     -} ->
  SetupValue       {- ^ second value to compare                    -} ->
  OverrideMatcher ()
learnEqual sc cc spec v1 v2 = do
  (_, val1) <- resolveSetupValueLLVM cc sc spec v1
  (_, val2) <- resolveSetupValueLLVM cc sc spec v2
  liftIO $ do
    p <- equalValsPred cc val1 val2
    let err = Crucible.AssertFailureSimError "equality precondition"
    Crucible.sbAddAssertion (ccBackend cc) p err

-- | Process a "crucible_precond" statement from the precondition
-- section of the CrucibleSetup block.
learnPred ::
  SharedContext                                                       ->
  CrucibleContext                                                     ->
  TypedTerm        {- ^ the precondition to learn                  -} ->
  OverrideMatcher ()
learnPred sc cc tt =
  do s <- OM (use termSub)
     t <- liftIO $ scInstantiateExt sc s (ttTerm tt)
     p <- liftIO $ resolveSAWPred cc t
     let err = Crucible.AssertFailureSimError "precondition"
     liftIO $ Crucible.sbAddAssertion (ccBackend cc) p err

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
     ptr <- liftSim $
       do mem <- Crucible.readGlobal memVar
          sz <- liftIO $ Crucible.bvLit sym Crucible.ptrWidth (fromIntegral w)
          (ptr, mem') <- liftIO (Crucible.doMalloc sym mem sz)
          Crucible.writeGlobal memVar mem'
          return ptr
     assignVar var ptr

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
executeSetupCondition sc cc spec (SetupCond_Equal val1 val2)  = executeEqual sc cc spec val1 val2
executeSetupCondition sc cc _    (SetupCond_Pred tm)          = executePred sc cc tm

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
  do liftIO $ putStrLn $ "Executing points to: " ++
                         show ptr ++ " -> " ++ show val
     (_, ptr1) <- asPointer =<< resolveSetupValue cc sc spec ptr
     sym    <- liftSim Crucible.getSymInterface

     (memTy1, val1) <- resolveSetupValue cc sc spec val
     storTy <- Crucible.toStorableType memTy1

     let memVar = Crucible.llvmMemVar $ Crucible.memModelOps $ ccLLVMContext cc
     liftSim $
       do mem  <- Crucible.readGlobal memVar
          mem' <- liftIO (Crucible.doStore sym mem ptr1 storTy val1)
          Crucible.writeGlobal memVar mem'


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
  liftIO $ do
    p <- equalValsPred cc val1 val2
    Crucible.sbAddAssumption (ccBackend cc) p

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
     liftIO $ Crucible.sbAddAssumption (ccBackend cc) p

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
     sym <- liftSim Crucible.getSymInterface
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

asPointer _ = fail "Not a pointer"
