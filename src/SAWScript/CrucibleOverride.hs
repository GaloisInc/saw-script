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

module SAWScript.CrucibleOverride (methodSpecHandler) where

import           Control.Lens
import           Control.Exception
import           Control.Monad.State
import           Data.Foldable (traverse_)
import           Data.List (tails)
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Vector as V

import qualified Text.LLVM.AST as L

import qualified Lang.Crucible.Core as Crucible
import qualified Lang.Crucible.Simulator.MSSim as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible

import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
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
  = OM { unOM :: forall rtp l.
        StateT
          OverrideState
          (Crucible.MSSim Sym rtp l 'Nothing)
          a }

data OverrideState = OverrideState
  { _setupValueSub :: Map AllocIndex
                        (Crucible.MemType,
                         Crucible.RegValue Sym Crucible.LLVMPointerType)
  , _termSub       :: Map VarIndex Term
  }

data OverrideFailure
  = BadSymType Crucible.SymType
  | AmbiguousPrecondition [SetupCondition]
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
  Crucible.OverrideSim Sym rtp args ret (Crucible.RegValue Sym ret)
methodSpecHandler sc cc cs retTy = do
  let L.Symbol fsym = csName cs
  liftIO $ putStrLn $ "Executing override for `" ++ fsym ++ "` (TODO)"

  Crucible.RegMap args <- Crucible.getOverrideArgs
  runOverrideMatcher $
    do args' <- (traverse . _1) resolveMemType (Map.elems (csArgBindings cs))

       -- todo: fail if list lengths mismatch
       zipWithM_ matchArg (assignmentToList args) args'
       processPreconditions sc cc (csPreconditions cs)
       enforceDisjointness cc
       traverse_ (executeSetupCondition sc cc) (csPostconditions cs)
       computeReturnValue cc sc retTy (csRetValue cs)

------------------------------------------------------------------------

-- | Generate assertions that all of the memory allocations matched by
-- an override's precondition are disjoint.
enforceDisjointness :: CrucibleContext -> OverrideMatcher ()
enforceDisjointness cc =
  do sym <- liftSim Crucible.getSymInterface
     m   <- Map.elems <$> OM (use setupValueSub)

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

processPreconditions ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext    {- ^ term construction context -} ->
  CrucibleContext  {- ^ simulator context         -} ->
  [SetupCondition] {- ^ preconditions             -} ->
  OverrideMatcher ()
processPreconditions sc cc = go False []
  where
    go ::
      Bool             {- progress indicator -} ->
      [SetupCondition] {- delayed conditions -} ->
      [SetupCondition] {- queued conditions  -} ->
      OverrideMatcher ()

    -- all conditions processed, success
    go _ [] [] = return ()

    -- not all conditions processed, no progress, failure
    go False delayed [] = failure (AmbiguousPrecondition delayed)

    -- not all conditions processed, progress made, resume delayed conditions
    go True delayed [] = go False [] delayed

    -- progress the next precondition in the work queue
    go progress delayed (c:cs) =
      do ready <- checkSetupCondition c
         if ready then
           do learnSetupCondition sc cc c
              go True delayed cs
         else
           do go progress (c:delayed) cs

    -- determine if a precondition is ready to be checked
    checkSetupCondition :: SetupCondition -> OverrideMatcher Bool
    checkSetupCondition (SetupCond_PointsTo p _) = checkSetupValue p
    checkSetupCondition SetupCond_Equal{}        = pure True

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
  Crucible.TypeRepr ret {- ^ representation of function return type -} ->
  Maybe SetupValue      {- ^ optional symbolic return value         -} ->
  OverrideMatcher (Crucible.RegValue Sym ret)
                        {- ^ concrete return value                  -}

computeReturnValue _ _ ty Nothing =
  case ty of
    Crucible.UnitRepr -> return ()
    _ -> fail "computeReturnValue: missing crucible_return specification"

computeReturnValue cc sc ty (Just val) =
  do (_memTy, Crucible.AnyValue xty xval) <- resolveSetupValue cc sc val
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

liftSim :: (forall rtp l. Crucible.MSSim Sym rtp l 'Nothing a) -> OverrideMatcher a
liftSim m = OM (lift m)

------------------------------------------------------------------------

-- | "Run" function for OverrideMatcher.
runOverrideMatcher ::
  OverrideMatcher a ->
  Crucible.OverrideSim Sym rtp l r a
runOverrideMatcher (OM m) = evalStateT m initialState

------------------------------------------------------------------------

assignVar ::
  AllocIndex                                     {- ^ variable index -} ->
  Crucible.MemType                               {- ^ LLVM type      -} ->
  Crucible.RegValue Sym Crucible.LLVMPointerType {- ^ concrete value -} ->
  OverrideMatcher ()

assignVar var memTy val =
  OM $ zoom (setupValueSub . at var) $

  do old <- get
     case old of
       Nothing -> put (Just (memTy, val))
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
  Crucible.AnyValue Sym          {- ^ concrete simulation value    -} ->
  (Crucible.MemType, SetupValue) {- ^ expected specification value -} ->
  OverrideMatcher ()
matchArg (Crucible.AnyValue ty val) (memTy, setupVal) = matchArg' ty memTy val setupVal

matchArg' ::
  Crucible.TypeRepr tp     {- ^ actual type         -} ->
  Crucible.MemType         {- ^ expected type       -} ->
  Crucible.RegValue Sym tp {- ^ actual value        -} ->
  SetupValue               {- ^ expected value      -} ->
  OverrideMatcher ()

matchArg' ty memTy val (SetupVar var) =
  case ty of
    Crucible.LLVMPointerRepr -> assignVar var memTy val
    _ -> fail "matchArg': expected pointer value"

-- match the fields of struct point-wise
matchArg'
  (Crucible.StructRepr xs) (Crucible.StructType fields)
  ys                       (SetupStruct zs) =
  zipWithM_
    matchArg
    (assignmentToList $
     Ctx.zipWith (\x (Crucible.RV y) -> Crucible.RegEntry x y) xs ys)
    (zip (V.toList (Crucible.fiType <$> Crucible.siFields fields)) zs)

matchArg'
  realTy _
  realVal (SetupTerm (TypedTerm _expectedTermTy expectedTerm)) =

  case Crucible.asBaseType realTy of
    Crucible.NotBaseType  -> fail "Unable to export value to SAW term"
    Crucible.AsBaseType _ ->
      do sym      <- liftSim Crucible.getSymInterface
         realTerm <- liftIO (Crucible.toSC sym realVal)
         matchTerm realTerm expectedTerm

matchArg' realTy expectedTy _ expected =
  fail $ "Argument mismatch: " ++
          show realTy ++ ", " ++
          show expected ++ " : " ++ show expectedTy


------------------------------------------------------------------------

matchTerm ::
  Term {- ^ exported concrete term      -} ->
  Term {- ^ expected specification term -} ->
  OverrideMatcher ()

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
  SetupCondition             ->
  OverrideMatcher ()
learnSetupCondition sc cc (SetupCond_PointsTo ptr val)   = learnPointsTo sc cc ptr val
learnSetupCondition _  _  (SetupCond_Equal ty val1 val2) = learnEqual ty val1 val2


------------------------------------------------------------------------

-- | Process a "points_to" statement from the precondition section of
-- the CrucibleSetup block. First, load the value from the address
-- indicated by 'ptr', and then match it against the pattern 'val'.
learnPointsTo ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  SetupValue {- ^ pointer -} ->
  SetupValue {- ^ value   -} ->
  OverrideMatcher ()
learnPointsTo sc cc ptr val =
  do liftIO $ putStrLn $ "Checking points to: " ++
                         show ptr ++ " -> " ++ show val
     (memTy,ptr1) <- asPointer =<< resolveSetupValue cc sc ptr
     storTy <- Crucible.toStorableType memTy
     sym    <- liftSim Crucible.getSymInterface

     mem    <- liftSim
             $ Crucible.readGlobal $ Crucible.llvmMemVar
             $ Crucible.memModelOps $ ccLLVMContext cc

     v      <- liftIO (Crucible.doLoad sym mem ptr1 storTy)
     matchArg v (memTy, val)


------------------------------------------------------------------------


-- | Process a "crucible_equal" statement from the precondition
-- section of the CrucibleSetup block.
learnEqual ::
  Crucible.SymType {- ^ type of values to be compared for equality -} ->
  SetupValue       {- ^ first value to compare                     -} ->
  SetupValue       {- ^ second value to compare                    -} ->
  OverrideMatcher ()
learnEqual _ _ _ = fail "learnEqual: incomplete"


------------------------------------------------------------------------

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
executeSetupCondition ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  SetupCondition             ->
  OverrideMatcher ()
executeSetupCondition sc cc (SetupCond_PointsTo ptr val)   = executePointsTo sc cc ptr val
executeSetupCondition _  _  (SetupCond_Equal ty val1 val2) = executeEqual ty val1 val2

------------------------------------------------------------------------

-- | Process a "points_to" statement from the postcondition section of
-- the CrucibleSetup block. First we compute the value indicated by
-- 'val', and then write it to the address indicated by 'ptr'.
executePointsTo ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  SetupValue {- ^ pointer -} ->
  SetupValue {- ^ value   -} ->
  OverrideMatcher ()
executePointsTo sc cc ptr val =
  do liftIO $ putStrLn $ "Executing points to: " ++
                         show ptr ++ " -> " ++ show val
     (memTy,ptr1) <- asPointer =<< resolveSetupValue cc sc ptr
     sym    <- liftSim Crucible.getSymInterface

     (memTy1, val1) <- resolveSetupValue cc sc val

     unless (TyCtx.compatMemTypes memTy memTy1) (fail "Mismatched store type")

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
  Crucible.SymType {- ^ type of values          -} ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher ()
executeEqual _ _ _ = fail "executeEqual: incomplete"


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
    SetupNull      -> return v
    SetupGlobal _  -> return v
  where
    doTerm (TypedTerm schema t) = TypedTerm schema <$> scInstantiateExt sc s t

------------------------------------------------------------------------

resolveSetupValue ::
  CrucibleContext ->
  SharedContext   ->
  SetupValue      ->
  OverrideMatcher (Crucible.MemType, Crucible.AnyValue Sym)
resolveSetupValue cc sc sval =
  do m <- OM (use setupValueSub)
     s <- OM (use termSub)
     let dl = TyCtx.llvmDataLayout (Crucible.llvmTypeCtx (ccLLVMContext cc))
     memTy <- liftIO $ typeOfSetupValue dl (fmap fst m) sval
     sval' <- liftIO $ instantiateSetupValue sc s sval
     let env = fmap (packPointer . snd) m
     lval <- liftIO $ resolveSetupVal cc env sval'
     sym <- liftSim Crucible.getSymInterface
     aval <- liftIO $ Crucible.unpackMemValue sym lval
     return (memTy, aval)

packPointer ::
  Crucible.RegValue Sym Crucible.LLVMPointerType ->
  Crucible.LLVMVal Sym Crucible.PtrWidth
packPointer (Crucible.RolledType xs) = Crucible.LLVMValPtr blk end off
  where
    Crucible.RV blk = xs^._1
    Crucible.RV end = xs^._2
    Crucible.RV off = xs^._3

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
