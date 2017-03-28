{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE TemplateHaskell #-}

module SAWScript.CrucibleOverride (methodSpecHandler) where

import           Control.Lens
import           Control.Monad.State
import           Data.Foldable (traverse_)
import           Data.Traversable
import           Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Vector as V

import qualified Text.LLVM.AST as L

import qualified Cryptol.TypeCheck.AST as Cryptol

import qualified Lang.Crucible.Core as Crucible
import qualified Lang.Crucible.Simulator.MSSim as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible

import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible

import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as NatRepr

import           Verifier.SAW.SharedTerm
import           Verifier.SAW.TypedAST

import           SAWScript.Builtins
import           SAWScript.CrucibleMethodSpecIR
import           SAWScript.TypedTerm

-- | The 'OverrideMatcher' type provides the operations that are needed
-- to match a specification's arguments with the arguments provided by
-- the Crucible simulation in order to compute the variable substitution
-- and side-conditions needed to proceed.
newtype OverrideMatcher rtp l r a
  = OverrideMatcher
      (StateT
        OverrideState
        (Crucible.OverrideSim Sym rtp l r)
        a)
  deriving (Functor, Applicative, Monad, MonadIO)

data OverrideState = OverrideState
  { _setupValueSub :: Map Integer (Crucible.MemType, Crucible.AnyValue Sym)
  , _termSub       :: Map VarIndex Term
  }

makeLenses ''OverrideState

initialState :: OverrideState
initialState = OverrideState Map.empty Map.empty

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
  let (L.Symbol fsym) = L.defName (csDefine cs)
  liftIO $ putStrLn $ "Executing override for `" ++ fsym ++ "` (TODO)"

  Crucible.RegMap args <- Crucible.getOverrideArgs
  runOverrideMatcher $
    do args' <- for (Map.elems (csArgBindings cs)) $ \(ty,val) ->
                        do ty' <- maybe (fail "Not a mem type") return
                                $ TyCtx.asMemType ty
                           return (ty',val)

       zipWithM_ matchArg (assignmentToList args) args'
       traverse_ (learnSetupCondition   sc cc) (csPreconditions  cs)
       traverse_ (executeSetupCondition sc cc) (csPostconditions cs)
       computeReturnValue sc retTy (csRetValue cs)

------------------------------------------------------------------------

computeReturnValue ::
  SharedContext         {- ^ context for generating saw terms       -} ->
  Crucible.TypeRepr ret {- ^ representation of function return type -} ->
  Maybe BindingPair     {- ^ optional symbolic return value         -} ->
  OverrideMatcher rtp l r (Crucible.RegValue Sym ret)
                        {- ^ concrete return value                  -}

computeReturnValue _ Crucible.UnitRepr _ = return ()

computeReturnValue sc ty (Just (BP _symTy (VarBind_Value val))) =
  do (_memTy, Crucible.AnyValue xty xval) <- resolveSetupValue sc val
     case NatRepr.testEquality ty xty of
       Just NatRepr.Refl -> return xval
       Nothing   -> fail "computeReturnValue: Unexpected return type"

computeReturnValue _ _ _ = fail "computeReturnValue: unsupported return value"


------------------------------------------------------------------------

-- | Forget the type indexes and length of the arguments.
assignmentToList ::
  Ctx.Assignment (Crucible.RegEntry sym) ctx ->
  [Crucible.AnyValue sym]
assignmentToList = Ctx.toListFC (\(Crucible.RegEntry x y) -> Crucible.AnyValue x y)

------------------------------------------------------------------------

liftSim :: Crucible.OverrideSim Sym rtp l r a -> OverrideMatcher rtp l r a
liftSim = OverrideMatcher . lift

------------------------------------------------------------------------

-- | "Run" function for OverrideMatcher.
runOverrideMatcher ::
  OverrideMatcher rtp l r a ->
  Crucible.OverrideSim Sym rtp l r a
runOverrideMatcher (OverrideMatcher m) = evalStateT m initialState

------------------------------------------------------------------------

assignVar ::
  Integer               {- ^ variable index -} ->
  Crucible.MemType      {- ^ LLVM type      -} ->
  Crucible.AnyValue Sym {- ^ concrete value -} ->
  OverrideMatcher rtp l r ()

assignVar var memTy val =
  OverrideMatcher             $
  zoom (setupValueSub . at var) $

  do old <- get
     case old of
       Nothing -> put (Just (memTy, val))
       Just _  -> fail "Unifying multiple occurrences of variables not yet supported"

------------------------------------------------------------------------


assignTerm ::
  VarIndex {- ^ external constant index -} ->
  Term     {- ^ value                   -} ->
  OverrideMatcher rtp l r ()

assignTerm var val =
  OverrideMatcher $
  zoom (termSub . at var) $

  do old <- get
     case old of
       Nothing -> put (Just val)
       Just _  -> fail "Unifying multiple occurrences of variables not yet supported"


------------------------------------------------------------------------

matchArg ::
  Crucible.AnyValue Sym          {- ^ concrete simulation value    -} ->
  (Crucible.MemType, SetupValue) {- ^ expected specification value -} ->
  OverrideMatcher rtp l r ()
matchArg (Crucible.AnyValue ty val) (memTy, setupVal) = matchArg' ty memTy val setupVal

matchArg' ::
  Crucible.TypeRepr tp     {- ^ actual type         -} ->
  Crucible.MemType         {- ^ expected type       -} ->
  Crucible.RegValue Sym tp {- ^ actual value        -} ->
  SetupValue               {- ^ expected value      -} ->
  OverrideMatcher rtp l r ()

matchArg' ty memTy val (SetupVar var) =
  assignVar var memTy (Crucible.AnyValue ty val)

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
  OverrideMatcher rtp l r ()

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
  OverrideMatcher rtp l r ()
learnSetupCondition sc cc (SetupCond_PointsTo ptr val)   = learnPointsTo sc cc ptr val
learnSetupCondition _  _  (SetupCond_Equal ty val1 val2) = learnEqual ty val1 val2


------------------------------------------------------------------------


learnPointsTo ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  SetupValue {- ^ pointer -} ->
  SetupValue {- ^ value   -} ->
  OverrideMatcher rtp l r ()
learnPointsTo sc cc ptr val =
  do liftIO $ putStrLn $ "Checking points to: " ++
                         show ptr ++ " -> " ++ show val
     (memTy,ptr1) <- asPointer =<< resolveSetupValue sc ptr
     storTy <- Crucible.toStorableType memTy
     sym    <- liftSim Crucible.getSymInterface

     mem    <- liftSim
             $ Crucible.readGlobal $ Crucible.llvmMemVar
             $ Crucible.memModelOps $ ccLLVMContext cc

     v      <- liftIO (Crucible.doLoad sym mem ptr1 storTy)
     matchArg v (memTy, val)


------------------------------------------------------------------------


learnEqual ::
  Crucible.SymType {- ^ type of values to be compared for equality -} ->
  SetupValue       {- ^ first value to compare                     -} ->
  SetupValue       {- ^ second value to compare                    -} ->
  OverrideMatcher rtp l r ()
learnEqual _ _ _ = fail "learnEqual: incomplete"


------------------------------------------------------------------------

-- | Use the current state to learn about variable assignments based on
-- preconditions for a procedure specification.
executeSetupCondition ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  SetupCondition             ->
  OverrideMatcher rtp l r ()
executeSetupCondition sc cc (SetupCond_PointsTo ptr val)   = executePointsTo sc cc ptr val
executeSetupCondition _  _  (SetupCond_Equal ty val1 val2) = executeEqual ty val1 val2

------------------------------------------------------------------------

executePointsTo ::
  (?lc :: TyCtx.LLVMContext) =>
  SharedContext              ->
  CrucibleContext            ->
  SetupValue {- ^ pointer -} ->
  SetupValue {- ^ value   -} ->
  OverrideMatcher rtp l r ()
executePointsTo sc cc ptr val =
  do liftIO $ putStrLn $ "Executing points to: " ++
                         show ptr ++ " -> " ++ show val
     (memTy,ptr1) <- asPointer =<< resolveSetupValue sc ptr
     sym    <- liftSim Crucible.getSymInterface

     (memTy1, val1) <- resolveSetupValue sc val

     unless (memTy == memTy1) (fail "Mismatched store type")

     storTy <- Crucible.toStorableType memTy1

     let memVar = Crucible.llvmMemVar $ Crucible.memModelOps $ ccLLVMContext cc
     liftSim $
       do mem  <- Crucible.readGlobal memVar
          mem' <- liftIO (Crucible.doStore sym mem ptr1 storTy val1)
          Crucible.writeGlobal memVar mem'


------------------------------------------------------------------------


executeEqual ::
  Crucible.SymType {- ^ type of values          -} ->
  SetupValue       {- ^ first value to compare  -} ->
  SetupValue       {- ^ second value to compare -} ->
  OverrideMatcher rtp l r ()
executeEqual _ _ _ = fail "executeEqual: incomplete"


------------------------------------------------------------------------

resolveSetupValue ::
  SharedContext ->
  SetupValue    ->
  OverrideMatcher rtp l r (Crucible.MemType, Crucible.AnyValue Sym)

resolveSetupValue _ (SetupVar i) =
  do v <- OverrideMatcher (use (setupValueSub . at i))
     case v of
       Nothing -> fail "Unknown variable"
       Just x  -> return x

resolveSetupValue
  sc
  (SetupTerm
     (TypedTerm
       (Cryptol.Forall [] []
          (Cryptol.TCon
             (Cryptol.TC Cryptol.TCSeq)
             [Cryptol.TCon (Cryptol.TC (Cryptol.TCNum sz)) [],
              Cryptol.TCon (Cryptol.TC Cryptol.TCBit) []]))
       t))
  | Just (Crucible.Some w) <- Crucible.someNat sz
  , Just Crucible.LeqProof <- Crucible.isPosNat w
  =

  do s   <- OverrideMatcher (use termSub)
     sym <- liftSim Crucible.getSymInterface
     t'  <- liftIO (scInstantiateExt sc s t)
     let ty = Crucible.BaseBVRepr w
     elt <- liftIO (Crucible.bindSAWTerm sym ty t')
     return (Crucible.IntType (fromInteger sz), Crucible.AnyValue (Crucible.BVRepr w) elt)

resolveSetupValue _ v =
   fail $ "resolveSetupValue: not implemented: " ++ show v


------------------------------------------------------------------------


asPointer ::
  (?lc :: TyCtx.LLVMContext) =>
  (Crucible.MemType, Crucible.AnyValue Sym) ->
  OverrideMatcher rtp l r
    (Crucible.MemType, Crucible.RegValue Sym Crucible.LLVMPointerType)

asPointer
  (Crucible.PtrType pty,
   Crucible.AnyValue (Crucible.RecursiveRepr ty) val)
  | Just pty'          <- TyCtx.asMemType pty
  , Just Crucible.Refl <-
        Crucible.testEquality ty
          (Crucible.knownSymbol :: Crucible.SymbolRepr "LLVM_pointer")
  = return (pty', val)

asPointer _ = fail "Not a pointer"
