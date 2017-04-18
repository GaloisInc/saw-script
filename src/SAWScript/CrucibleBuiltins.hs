{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}

{- |
Module           : $Header$
Description      :
License          : BSD3
Stability        : provisional
Point-of-contact : atomb
-}
module SAWScript.CrucibleBuiltins where

import Control.Lens
import Control.Monad.ST
import Control.Monad.State
import Control.Applicative
import Data.Maybe (fromMaybe)
import Data.Foldable (toList, find)
import Data.IORef
import Data.String
import System.IO
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Map (Map)
import qualified Data.Map as Map
--import qualified Data.Text as Text
import qualified Data.Vector as V

import qualified Data.LLVM.BitCode as L
import qualified Text.LLVM.AST as L
import qualified Text.LLVM.PP as L (ppType, ppSymbol)
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import qualified Data.Parameterized.Nonce as Crucible
import qualified Lang.Crucible.Config as Crucible
import qualified Lang.Crucible.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator.CallFns as Crucible
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible
import qualified Lang.Crucible.Simulator.MSSim as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible
import qualified Lang.Crucible.Solver.Interface as Crucible hiding (mkStruct)
import qualified Lang.Crucible.Solver.SimpleBuilder as Crucible
import qualified Lang.Crucible.Solver.Symbol as Crucible

import qualified Lang.Crucible.LLVM as Crucible
import qualified Lang.Crucible.LLVM.DataLayout as Crucible
import qualified Lang.Crucible.LLVM.MemType as Crucible
import qualified Lang.Crucible.LLVM.LLVMContext as TyCtx
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.LLVM.MemModel as Crucible
import qualified Lang.Crucible.LLVM.MemModel.Common as Crucible
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible
-- import           Lang.Crucible.Utils.MonadST
import qualified Data.Parameterized.TraversableFC as Ctx
import qualified Data.Parameterized.Context as Ctx

import Verifier.SAW.Prelude
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedAST

import SAWScript.Builtins
import SAWScript.Options
import SAWScript.Proof
import SAWScript.TypedTerm
import SAWScript.TopLevel
import SAWScript.Value

import SAWScript.CrucibleMethodSpecIR
import SAWScript.CrucibleOverride
import SAWScript.CrucibleResolveSetupValue


type MemImpl = Crucible.MemImpl Sym Crucible.PtrWidth

--import qualified SAWScript.LLVMBuiltins as LB

show_cfg :: Crucible.AnyCFG -> String
show_cfg (Crucible.AnyCFG cfg) = show cfg


-- | Abort the current execution.
abortTree :: Crucible.SimError
          -> Crucible.MSS_State  sym rtp f args
          -> IO (Crucible.SimResult  sym rtp)
abortTree e s = do
  -- Switch to new frame.
  Crucible.isSolverProof (s^.Crucible.stateContext) $ do
    Crucible.abortExec e s


errorHandler :: Crucible.ErrorHandler Crucible.SimContext sym rtp
errorHandler = Crucible.EH abortTree

ppAbortedResult :: CrucibleContext
                -> Crucible.AbortedResult (Crucible.MSS_State Sym)
                -> IO Doc
ppAbortedResult cc (Crucible.AbortedExec err gp) = do
  memDoc <- ppGlobalPair cc gp
  return (Crucible.ppSimError err <$$> memDoc)
ppAbortedResult _ (Crucible.AbortedBranch _ _ _) =
    return (text "Aborted branch")

crucible_llvm_verify ::
  BuiltinContext         ->
  Options                ->
  String                 ->
  [CrucibleMethodSpecIR] ->
  CrucibleSetup ()       ->
  ProofScript SatResult  ->
  TopLevel CrucibleMethodSpecIR
crucible_llvm_verify bic _opts nm lemmas setup tactic =
  do cc <- io $ readIORef (biCrucibleContext bic) >>= \case
              Nothing -> fail "No Crucible LLVM module loaded"
              Just cc -> return cc
     let ?lc = Crucible.llvmTypeCtx (ccLLVMContext cc)
     let nm' = fromString nm
     let llmod = ccLLVMModule cc
     def <- case find (\d -> L.defName d == nm') (L.modDefines llmod) of
                    Nothing -> fail ("Could not find function named" ++ show nm)
                    Just decl -> return decl
     let st0 = initialCrucibleSetupState def
     methodSpec <- csMethodSpec <$> execStateT setup st0
     let globals = ccGlobals cc
     let memOps = Crucible.memModelOps (ccLLVMContext cc)
     mem0 <- case Crucible.lookupGlobal (Crucible.llvmMemVar memOps) globals of
       Nothing -> fail "internal error: LLVM Memory global not found"
       Just mem0 -> return mem0
     --io $ putStrLn $ unlines [ "Method Spec:", show methodSpec]
     (args, assumes, env, mem1) <- io $ verifyPrestate cc methodSpec mem0
     (ret, mem2) <- io $ verifySimulate cc methodSpec args assumes lemmas mem1
     asserts <- io $ verifyPoststate cc methodSpec env mem2 ret
     verifyObligations cc methodSpec tactic assumes asserts
     return methodSpec

crucible_llvm_unsafe_assume_spec ::
  BuiltinContext   ->
  Options          ->
  String           ->
  CrucibleSetup () ->
  TopLevel CrucibleMethodSpecIR
crucible_llvm_unsafe_assume_spec bic _opts nm setup = do
  cc <- io $ readIORef (biCrucibleContext bic) >>= \case
           Nothing -> fail "No Crucible LLVM module loaded"
           Just cc -> return cc
  let ?lc = Crucible.llvmTypeCtx (ccLLVMContext cc)
  let nm' = fromString nm
  let llmod = ccLLVMModule cc
  st0 <- case initialCrucibleSetupState     <$> find (\d -> L.defName d == nm') (L.modDefines  llmod) <|>
              initialCrucibleSetupStateDecl <$> find (\d -> L.decName d == nm') (L.modDeclares llmod) of
                 Nothing -> fail ("Could not find function named" ++ show nm)
                 Just st0 -> return st0
  csMethodSpec <$> execStateT setup st0

verifyObligations :: CrucibleContext
                  -> CrucibleMethodSpecIR
                  -> ProofScript SatResult
                  -> [Term]
                  -> [Term]
                  -> TopLevel ()
verifyObligations cc mspec tactic assumes asserts = do
  let sym = ccBackend cc
  st     <- io $ readIORef $ Crucible.sbStateManager sym
  let sc  = Crucible.saw_ctx st
  t      <- io $ scBool sc True
  assume <- io $ foldM (scAnd sc) t assumes
  assert <- io $ foldM (scAnd sc) t asserts
  goal   <- io $ scImplies sc assume assert
  goal'  <- io $ scAbstractExts sc (getAllExts goal) goal
  let nm  = show (L.ppSymbol (csName mspec))
  r      <- evalStateT tactic (startProof (ProofGoal Universal nm goal'))
  case r of
    Unsat _stats -> do
      io $ putStrLn $ unwords ["Proof succeeded!", nm]
    SatMulti stats vals -> do
      io $ putStrLn $ unwords ["Proof failed!", nm]
      io $ print stats
      io $ mapM_ print vals

-- | Evaluate the precondition part of a Crucible method spec:
--
-- * Allocate heap space for each 'crucible_alloc' statement.
--
-- * Record an equality precondition for each 'crucible_equal'
-- statement.
--
-- * Write to memory for each 'crucible_points_to' statement. (Writes
-- to already-initialized locations are transformed into equality
-- preconditions.)
--
-- * Evaluate the function arguments from the 'crucible_execute_func'
-- statement.
--
-- Returns a tuple of (arguments, preconditions, pointer values,
-- memory).
verifyPrestate ::
  CrucibleContext ->
  CrucibleMethodSpecIR ->
  MemImpl ->
  IO ([(Crucible.MemType, LLVMVal)], [Term], Map AllocIndex LLVMVal, MemImpl)
verifyPrestate cc mspec mem = do
  let ?lc = Crucible.llvmTypeCtx (ccLLVMContext cc)
  -- Allocate LLVM memory for each 'crucible_alloc'
  (env1, mem') <- runStateT (traverse (doAlloc cc) (csAllocations mspec)) mem
  env2 <- Map.traverseWithKey (\k _ -> setupFreshPointer cc k) (csFreshPointers mspec)
  let env = Map.union env1 env2
  (cs, mem'') <- setupPrestateConditions mspec cc env (csPreconditions mspec) mem'
  args <- resolveArguments cc mspec env
  return (args, cs, env, mem'')


-- | Construct a completely symbolic pointer. This pointer could point to anything, or it could
-- be NULL.
setupFreshPointer ::
  CrucibleContext {- ^ Crucible context       -} ->
  AllocIndex      {- ^ SetupVar id            -} ->
  IO LLVMVal      {- ^ Symbolic pointer value -}
setupFreshPointer cc (AllocIndex i) =
  do let sym = ccBackend cc
         mkName base = Crucible.systemSymbol (base ++ show i ++ "!")
     blk <- Crucible.freshConstant sym (mkName "blk") Crucible.BaseNatRepr
     end <- Crucible.freshConstant sym (mkName "end") (Crucible.BaseBVRepr Crucible.ptrWidth)
     off <- Crucible.freshConstant sym (mkName "off") (Crucible.BaseBVRepr Crucible.ptrWidth)
     return (Crucible.LLVMValPtr blk end off)

resolveArguments ::
  (?lc :: TyCtx.LLVMContext) =>
  CrucibleContext            ->
  CrucibleMethodSpecIR       ->
  Map AllocIndex LLVMVal     ->
  IO [(Crucible.MemType, LLVMVal)]
resolveArguments cc mspec env = mapM resolveArg [0..(nArgs-1)]
 where
  nArgs = toInteger (length (csArgs mspec))
  tyenv = csAllocations mspec
  resolveArg i =
    case Map.lookup i (csArgBindings mspec) of
      Just (tp, sv) -> do
        let mt = fromMaybe (error ("Expected memory type:" ++ show tp)) (TyCtx.asMemType tp)
        v <- resolveSetupVal cc env tyenv sv
        return (mt, v)
      Nothing -> fail $ unwords ["Argument", show i, "unspecified"]

--------------------------------------------------------------------------------

setupPrestateConditions ::
  (?lc :: TyCtx.LLVMContext) =>
  CrucibleMethodSpecIR       ->
  CrucibleContext            ->
  Map AllocIndex LLVMVal     ->
  [SetupCondition]           ->
  MemImpl                    ->
  IO ([Term], MemImpl)
setupPrestateConditions mspec cc env conds mem0 =
  foldM go ([], mem0) conds
  where
    tyenv = csAllocations mspec

    go :: ([Term], MemImpl) -> SetupCondition -> IO ([Term], MemImpl)
    go (cs, mem) (SetupCond_PointsTo ptr val) =
      do val' <- resolveSetupVal cc env tyenv val
         ptr' <- resolveSetupVal cc env tyenv ptr
         ptr'' <- case ptr' of
           Crucible.LLVMValPtr blk end off -> return (Crucible.LLVMPtr blk end off)
           _ -> fail "Non-pointer value found in points-to assertion"
         lhsTy <- case typeOfSetupValue cc (csAllocations mspec) ptr of
           Just (Crucible.PtrType symTy) ->
             case TyCtx.asMemType symTy of
               Just lhsTy -> return lhsTy
               Nothing -> fail $ "lhs not a valid pointer type: " ++ show symTy
           _ -> fail $ "lhs not a pointer type"
         storTy <- case Crucible.toStorableType lhsTy of
           Just storTy -> return storTy
           Nothing -> fail $ "Expected memory type: " ++ show lhsTy
         let sym = ccBackend cc
         mem' <- Crucible.storeRaw sym mem ptr'' storTy val'
         return (cs, mem')

    go (cs, mem) (SetupCond_Equal val1 val2) =
      do val1' <- resolveSetupVal cc env tyenv val1
         val2' <- resolveSetupVal cc env tyenv val2
         c <- assertEqualVals cc val1' val2'
         return (c : cs, mem)

--------------------------------------------------------------------------------

-- | Create a SAWCore formula asserting that two 'LLVMVal's are equal.
assertEqualVals ::
  CrucibleContext ->
  LLVMVal ->
  LLVMVal ->
  IO Term
assertEqualVals cc v1 v2 = Crucible.toSC sym =<< go (v1, v2)
 where
  go :: (LLVMVal, LLVMVal) -> IO (Crucible.Pred Sym)

  go (Crucible.LLVMValPtr blk1 _end1 off1, Crucible.LLVMValPtr blk2 _end2 off2)
       = do blk_eq <- Crucible.natEq sym blk1 blk2
            off_eq <- Crucible.bvEq sym off1 off2
            Crucible.andPred sym blk_eq off_eq
  go (Crucible.LLVMValFunPtr _ _ _fn1, Crucible.LLVMValFunPtr _ _ _fn2)
       = fail "Cannot compare function pointers for equality FIXME"
  go (Crucible.LLVMValInt wx x, Crucible.LLVMValInt wy y)
       | Just Crucible.Refl <- Crucible.testEquality wx wy
       = Crucible.bvEq sym x y
  go (Crucible.LLVMValReal x, Crucible.LLVMValReal y)
       = Crucible.realEq sym x y
  go (Crucible.LLVMValStruct xs, Crucible.LLVMValStruct ys)
       | V.length xs == V.length ys
       = do cs <- mapM go (zip (map snd (toList xs)) (map snd (toList ys)))
            foldM (Crucible.andPred sym) (Crucible.truePred sym) cs
  go (Crucible.LLVMValArray _tpx xs, Crucible.LLVMValArray _tpy ys)
       | V.length xs == V.length ys
       = do cs <- mapM go (zip (toList xs) (toList ys))
            foldM (Crucible.andPred sym) (Crucible.truePred sym) cs

  go _ = return (Crucible.falsePred sym)

  sym = ccBackend cc

--------------------------------------------------------------------------------

asSAWType :: SharedContext
          -> Crucible.Type
          -> IO Term
asSAWType sc t = case Crucible.typeF t of
  Crucible.Bitvector bytes -> scBitvector sc (fromIntegral (bytes*8))
  Crucible.Float           -> scGlobalDef sc (fromString "Prelude.Float")  -- FIXME??
  Crucible.Double          -> scGlobalDef sc (fromString "Prelude.Double") -- FIXME??
  Crucible.Array sz s ->
    do s' <- asSAWType sc s
       sz_tm <- scNat sc (fromIntegral sz)
       scVecType sc sz_tm s'
  Crucible.Struct flds ->
    do flds' <- mapM (asSAWType sc . (^. Crucible.fieldVal)) $ V.toList flds
       scTupleType sc flds'

--------------------------------------------------------------------------------

-- | Allocate space on the LLVM heap to store a value of the given
-- type. Returns the pointer to the allocated memory.
doAlloc ::
  (?lc :: TyCtx.LLVMContext) =>
  CrucibleContext            ->
  Crucible.MemType           ->
  StateT MemImpl IO LLVMVal
doAlloc cc tp = StateT $ \mem ->
  do let sym = ccBackend cc
     let dl = TyCtx.llvmDataLayout ?lc
     sz <- Crucible.bvLit sym Crucible.ptrWidth (fromIntegral (Crucible.memTypeSize dl tp))
     (Crucible.LLVMPtr blk end x, mem') <- Crucible.mallocRaw sym mem sz
     return (Crucible.LLVMValPtr blk end x, mem')

--------------------------------------------------------------------------------

ppGlobalPair :: CrucibleContext
             -> Crucible.GlobalPair (Crucible.MSS_State Sym) a
             -> IO Doc
ppGlobalPair cc gp =
  let memOps = Crucible.memModelOps (ccLLVMContext cc)
      sym = ccBackend cc
      globals = gp ^. Crucible.gpGlobals in
  case Crucible.lookupGlobal (Crucible.llvmMemVar memOps) globals of
    Nothing -> return (text "LLVM Memory global variable not initialized")
    Just mem -> Crucible.ppMem sym mem


--------------------------------------------------------------------------------

registerOverride ::
  (?lc :: TyCtx.LLVMContext) =>
  CrucibleContext            ->
  Crucible.SimContext Sym    ->
  CrucibleMethodSpecIR       ->
  Crucible.OverrideSim Sym rtp args ret ()
registerOverride cc _ctx cs = do
  let sym = ccBackend cc
  sc <- Crucible.saw_ctx <$> liftIO (readIORef (Crucible.sbStateManager sym))
  let s@(L.Symbol fsym) = csName cs
      llvmctx = ccLLVMContext cc
  liftIO $ putStrLn $ "Registering override for `" ++ fsym ++ "`"
  case Map.lookup s (llvmctx ^. Crucible.symbolMap) of
    -- LLVMHandleInfo constructor has two existential type arguments,
    -- which are bound here. h :: FnHandle args' ret'
    Just (Crucible.LLVMHandleInfo _decl' h) -> do
      -- TODO: check that decl' matches (csDefine cs)
      let retType = Crucible.handleReturnType h
      Crucible.registerFnBinding h
        $ Crucible.UseOverride
        $ Crucible.mkOverride'
            (Crucible.handleName h)
            retType
            (methodSpecHandler sc cc cs retType)
    Nothing -> fail $ "Can't find declaration for `" ++ fsym ++ "`."

--------------------------------------------------------------------------------

verifySimulate ::
  (?lc :: TyCtx.LLVMContext) =>
  CrucibleContext ->
  CrucibleMethodSpecIR ->
  [(Crucible.MemType, LLVMVal)] ->
  [Term] ->
  [CrucibleMethodSpecIR] ->
  MemImpl ->
  IO (Maybe LLVMVal, MemImpl)
verifySimulate cc mspec args _assumes lemmas mem =
  do let nm = csName mspec
     case Map.lookup nm (Crucible.cfgMap (ccLLVMModuleTrans cc)) of
       Nothing -> fail $ unwords ["function", show nm, "not found"]
       Just (Crucible.AnyCFG cfg) ->
         do let h   = Crucible.cfgHandle cfg
                rty = Crucible.handleReturnType h
            args' <- prepareArgs (Crucible.handleArgTypes h) (map snd args)
            let simCtx = ccSimContext cc
            let globals = Crucible.llvmGlobals (ccLLVMContext cc) mem
            res <-
              Crucible.run simCtx globals errorHandler rty $
              do mapM_ (registerOverride cc simCtx) lemmas
                 Crucible.regValue <$> (Crucible.callCFG cfg args')
            case res of
              Crucible.FinishedExecution _ pr ->
                do Crucible.GlobalPair retval globals' <-
                     case pr of
                       Crucible.TotalRes gp -> return gp
                       Crucible.PartialRes _ gp _ ->
                         do putStrLn "Symbolic simulation failed along some paths!"
                            return gp
                   let memOps = Crucible.memModelOps (ccLLVMContext cc)
                   mem' <- case Crucible.lookupGlobal (Crucible.llvmMemVar memOps) globals' of
                     Nothing -> fail "internal error: LLVM Memory global not found"
                     Just mem' -> return mem'
                   let ret_ty = csRet mspec
                   let ret_ty' = fromMaybe (error ("Expected return type:" ++ show ret_ty))
                                 (TyCtx.liftRetType ret_ty)
                   retval' <- case ret_ty' of
                     Nothing -> return Nothing
                     Just ret_mt -> Just <$>
                       Crucible.packMemValue (ccBackend cc)
                         (fromMaybe (error ("Expected storable type:" ++ show ret_ty))
                              (Crucible.toStorableType ret_mt))
                         (Crucible.regType  retval)
                         (Crucible.regValue retval)
                   return (retval', mem')

              Crucible.AbortedResult _ ar ->
                do resultDoc <- ppAbortedResult cc ar
                   fail $ unlines [ "Symbolic execution failed."
                                  , show resultDoc
                                  ]

  where
    prepareArgs ::
      Ctx.Assignment Crucible.TypeRepr xs ->
      [LLVMVal] ->
      IO (Crucible.RegMap Sym xs)
    prepareArgs ctx x =
      Crucible.RegMap <$>
      Ctx.traverseWithIndex (\idx tr ->
        do a <- Crucible.unpackMemValue (ccBackend cc) (x !! Ctx.indexVal idx)
           v <- Crucible.coerceAny (ccBackend cc) tr a
           return (Crucible.RegEntry tr v))
      ctx

--------------------------------------------------------------------------------

verifyPoststate ::
  (?lc :: TyCtx.LLVMContext) =>
  CrucibleContext ->
  CrucibleMethodSpecIR ->
  Map AllocIndex LLVMVal ->
  MemImpl ->
  Maybe LLVMVal ->
  IO [Term]
verifyPoststate cc mspec env mem ret =
  do goals <- mapM verifyPostCond (csPostconditions mspec)
     case (ret, csRetValue mspec) of
       (Nothing, Nothing) -> return goals
       (Nothing, Just _) -> fail "verifyPoststate: unexpected crucible_return specification"
       (Just _, Nothing) -> fail "verifyPoststate: missing crucible_return specification"
       (Just ret', Just val) ->
         do val' <- resolveSetupVal cc env tyenv val
            goal <- assertEqualVals cc ret' val'
            return (goal : goals)
  where
    dl = TyCtx.llvmDataLayout (Crucible.llvmTypeCtx (ccLLVMContext cc))
    tyenv = csAllocations mspec

    verifyPostCond (SetupCond_PointsTo lhs val) = do
      lhs' <- resolveSetupVal cc env tyenv lhs
      ptr <- case lhs' of
        Crucible.LLVMValPtr blk end off -> return (Crucible.LLVMPtr blk end off)
        _ -> fail "Non-pointer value found in points-to assertion"
      val' <- resolveSetupVal cc env tyenv val
      let tp' = typeOfLLVMVal dl val'
      let sym = ccBackend cc
      x <- Crucible.loadRaw sym mem ptr tp'
      assertEqualVals cc x val'

    verifyPostCond (SetupCond_Equal val1 val2) = do
      val1' <- resolveSetupVal cc env tyenv val1
      val2' <- resolveSetupVal cc env tyenv val2
      assertEqualVals cc val1' val2'

--------------------------------------------------------------------------------

load_crucible_llvm_module :: BuiltinContext -> Options -> String -> TopLevel ()
load_crucible_llvm_module bic opts bc_file = do
  halloc <- getHandleAlloc
  let r = biCrucibleContext bic
  io (L.parseBitCodeFromFile bc_file) >>= \case
    Left err -> fail (L.formatError err)
    Right llvm_mod -> io $ do
      (ctx, mtrans) <- stToIO $ Crucible.translateModule halloc llvm_mod
      let gen = Crucible.globalNonceGenerator
      let sc  = biSharedContext bic
      sym <- Crucible.newSAWCoreBackend sc gen
      let verbosity = simVerbose opts
      cfg <- Crucible.initialConfig verbosity []
      let bindings = Crucible.fnBindingsFromList []
      let simctx   = Crucible.initSimContext sym Crucible.llvmIntrinsicTypes cfg halloc stdout
                        bindings
      mem <- Crucible.initializeMemory sym ctx llvm_mod
      let globals  = Crucible.llvmGlobals ctx mem

      let setupMem :: Crucible.OverrideSim Sym
                       (Crucible.RegEntry Sym Crucible.UnitType)
                       Crucible.EmptyCtx Crucible.UnitType (Crucible.RegValue Sym Crucible.UnitType)
          setupMem = do
             -- register the callable override functions
             _llvmctx' <- execStateT Crucible.register_llvm_overrides ctx

             -- initialize LLVM global variables
             _ <- case Crucible.initMemoryCFG mtrans of
                     Crucible.SomeCFG initCFG ->
                       Crucible.callCFG initCFG Crucible.emptyRegMap

             -- register all the functions defined in the LLVM module
             mapM_ Crucible.registerModuleFn $ Map.toList $ Crucible.cfgMap mtrans

      res <- Crucible.run simctx globals errorHandler Crucible.UnitRepr setupMem
      (globals', simctx') <-
          case res of
            Crucible.FinishedExecution st (Crucible.TotalRes gp) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.FinishedExecution st (Crucible.PartialRes _ gp _) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.AbortedResult _ _ -> fail "Memory initialization failed!"
      writeIORef r $ Just
         CrucibleContext{ ccLLVMContext = ctx
                        , ccLLVMModuleTrans = mtrans
                        , ccLLVMModule = llvm_mod
                        , ccBackend = sym
                        , ccEmptyMemImpl = mem
                        , ccSimContext = simctx'
                        , ccGlobals = globals'
                        }

--------------------------------------------------------------------------------

setupArg :: SharedContext
         -> Sym
         -> IORef (Seq (ExtCns Term))
         -> Crucible.TypeRepr tp
         -> IO (Crucible.RegEntry Sym tp)
setupArg sc sym ecRef tp =
  case Crucible.asBaseType tp of
    Crucible.AsBaseType btp -> do
       sc_tp <- Crucible.baseSCType sc btp
       i     <- scFreshGlobalVar sc
       ecs   <- readIORef ecRef
       let len = Seq.length ecs
       let ec = EC i ("arg_"++show len) sc_tp
       writeIORef ecRef (ecs Seq.|> ec)
       t     <- scFlatTermF sc (ExtCns ec)
       elt   <- Crucible.bindSAWTerm sym btp t
       return (Crucible.RegEntry tp elt)

    Crucible.NotBaseType ->
      fail $ unwords ["Crucible extraction currently only supports Crucible base types", show tp]

setupArgs :: SharedContext
          -> Sym
          -> Crucible.FnHandle init ret
          -> IO (Seq (ExtCns Term), Crucible.RegMap Sym init)
setupArgs sc sym fn = do
  ecRef  <- newIORef Seq.empty
  regmap <- Crucible.RegMap <$> Ctx.traverseFC (setupArg sc sym ecRef) (Crucible.handleArgTypes fn)
  ecs    <- readIORef ecRef
  return (ecs, regmap)

--------------------------------------------------------------------------------

extractFromCFG :: SharedContext -> CrucibleContext -> Crucible.AnyCFG -> IO TypedTerm
extractFromCFG sc cc (Crucible.AnyCFG cfg) = do
  let sym = ccBackend cc
  let h   = Crucible.cfgHandle cfg
  (ecs, args) <- setupArgs sc sym h
  let simCtx = ccSimContext cc
  let globals = ccGlobals cc
  res  <- Crucible.run simCtx globals errorHandler (Crucible.handleReturnType h)
             (Crucible.regValue <$> (Crucible.callCFG cfg args))
  case res of
    Crucible.FinishedExecution _ pr -> do
        gp <- case pr of
                Crucible.TotalRes gp -> return gp
                Crucible.PartialRes _ gp _ -> do
                  putStrLn "Symbolic simulation failed along some paths!"
                  return gp
        t <- Crucible.asSymExpr
                   (gp^.Crucible.gpValue)
                   (Crucible.toSC sym)
                   (fail $ unwords ["Unexpected return type:", show (Crucible.regType (gp^.Crucible.gpValue))])
        t' <- scAbstractExts sc (toList ecs) t
        tt <- mkTypedTerm sc t'
        return tt
    Crucible.AbortedResult _ ar -> do
      resultDoc <- ppAbortedResult cc ar
      fail $ unlines [ "Symbolic execution failed."
                     , show resultDoc
                     ]

--------------------------------------------------------------------------------

extract_crucible_llvm :: BuiltinContext -> Options -> String -> TopLevel TypedTerm
extract_crucible_llvm bic _opts fn_name = do
  let r  = biCrucibleContext bic
  let sc = biSharedContext bic
  io (readIORef r) >>= \case
    Nothing -> fail "No Crucible LLVM module loaded"
    Just cc ->
      case Map.lookup (fromString fn_name) (Crucible.cfgMap (ccLLVMModuleTrans cc)) of
        Nothing  -> fail $ unwords ["function", fn_name, "not found"]
        Just cfg -> io $ do
           extractFromCFG sc cc cfg

load_llvm_cfg :: BuiltinContext -> Options -> String -> TopLevel Crucible.AnyCFG
load_llvm_cfg bic _opts fn_name = do
  let r = biCrucibleContext bic
  io (readIORef r) >>= \case
    Nothing -> fail "No Crucible LLVM module loaded"
    Just cc ->
      case Map.lookup (fromString fn_name) (Crucible.cfgMap (ccLLVMModuleTrans cc)) of
        Nothing  -> fail $ unwords ["function", fn_name, "not found"]
        Just cfg -> return cfg

--------------------------------------------------------------------------------

diffMemTypes ::
  Crucible.MemType ->
  Crucible.MemType ->
  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
diffMemTypes x0 y0 =
  case (x0, y0) of
    (Crucible.IntType x, Crucible.IntType y) | x == y -> []
    (Crucible.FloatType, Crucible.FloatType) -> []
    (Crucible.DoubleType, Crucible.DoubleType) -> []
    (Crucible.PtrType{}, Crucible.PtrType{}) -> []
    (Crucible.IntType 64, Crucible.PtrType{}) -> []
    (Crucible.PtrType{}, Crucible.IntType 64) -> []
    (Crucible.ArrayType xn xt, Crucible.ArrayType yn yt)
      | xn == yn ->
        [ (Nothing : path, l , r) | (path, l, r) <- diffMemTypes xt yt ]
    (Crucible.VecType xn xt, Crucible.VecType yn yt)
      | xn == yn ->
        [ (Nothing : path, l , r) | (path, l, r) <- diffMemTypes xt yt ]
    (Crucible.StructType x, Crucible.StructType y)
      | Crucible.siIsPacked x == Crucible.siIsPacked y
        && V.length (Crucible.siFields x) == V.length (Crucible.siFields y) ->
          let xts = Crucible.siFieldTypes x
              yts = Crucible.siFieldTypes y
          in diffMemTypesList 1 (V.toList (V.zip xts yts))
    _ -> [([], x0, y0)]

diffMemTypesList ::
  Int ->
  [(Crucible.MemType, Crucible.MemType)] ->
  [([Maybe Int], Crucible.MemType, Crucible.MemType)]
diffMemTypesList _ [] = []
diffMemTypesList i ((x, y) : ts) =
  [ (Just i : path, l , r) | (path, l, r) <- diffMemTypes x y ]
  ++ diffMemTypesList (i+1) ts

showMemTypeDiff :: ([Maybe Int], Crucible.MemType, Crucible.MemType) -> String
showMemTypeDiff (path, l, r) = showPath path
  where
    showStep Nothing = "element type"
    showStep (Just i) = "field " ++ show i
    showPath [] = ""
    showPath [x] = unlines [showStep x ++ ":", "  " ++ show l, "  " ++ show r]
    showPath (x : xs) = showStep x ++ " -> " ++ showPath xs

-- | Succeed if the types have compatible memory layouts. Otherwise,
-- fail with a detailed message indicating how the types differ.
checkMemTypeCompatibility ::
  Crucible.MemType ->
  Crucible.MemType ->
  CrucibleSetup ()
checkMemTypeCompatibility t1 t2 =
  case diffMemTypes t1 t2 of
    [] -> return ()
    diffs ->
      fail $ unlines $
      ["types not memory-compatible:", show t1, show t2]
      ++ map showMemTypeDiff diffs

--------------------------------------------------------------------------------
-- Setup builtins

getCrucibleContext :: BuiltinContext -> CrucibleSetup CrucibleContext
getCrucibleContext bic =
  lift (io (readIORef (biCrucibleContext bic))) >>= maybe (fail "No Crucible LLVM module loaded") return

addCondition :: SetupCondition
             -> CrucibleSetup ()
addCondition cond = do
  st <- get
  let spec = csMethodSpec st
      spec' = spec{ csConditions = (csPrePost st,cond) : csConditions spec }
  put st{ csMethodSpec = spec' }

-- | Returns logical type of actual type if it is an array or primitive
-- type, or an appropriately-sized bit vector for pointer types.
logicTypeOfActual :: Crucible.DataLayout -> SharedContext -> Crucible.MemType
                  -> IO (Maybe Term)
logicTypeOfActual _ sc (Crucible.IntType w) = do
  bType <- scBoolType sc
  lTm <- scNat sc (fromIntegral w)
  Just <$> scVecType sc lTm bType
logicTypeOfActual _ sc Crucible.FloatType = Just <$> scPrelude_Float sc
logicTypeOfActual _ sc Crucible.DoubleType = Just <$> scPrelude_Double sc
logicTypeOfActual dl sc (Crucible.ArrayType n ty) = do
  melTyp <- logicTypeOfActual dl sc ty
  case melTyp of
    Just elTyp -> do
      lTm <- scNat sc (fromIntegral n)
      Just <$> scVecType sc lTm elTyp
    Nothing -> return Nothing
logicTypeOfActual dl sc (Crucible.PtrType _) = do
  bType <- scBoolType sc
  lTm <- scNat sc (fromIntegral (Crucible.ptrBitwidth dl))
  Just <$> scVecType sc lTm bType
logicTypeOfActual dl sc (Crucible.StructType si) = do
  let memtypes = V.toList (Crucible.siFieldTypes si)
  melTyps <- traverse (logicTypeOfActual dl sc) memtypes
  case sequence melTyps of
    Just elTyps -> Just <$> scTupleType sc elTyps
    Nothing -> return Nothing
logicTypeOfActual _ _ _ = return Nothing


crucible_fresh_var :: BuiltinContext
                   -> Options
                   -> String
                   -> L.Type
                   -> CrucibleSetup TypedTerm
crucible_fresh_var bic _opts name lty = do
  cctx <- lift (io (readIORef (biCrucibleContext bic))) >>= maybe (fail "No Crucible LLVM module loaded") return
  let sc = biSharedContext bic
  let lc = ccLLVMContext cctx
  let ?lc = Crucible.llvmTypeCtx lc
  let dl = TyCtx.llvmDataLayout (Crucible.llvmTypeCtx lc)
  lty' <- case TyCtx.liftMemType lty of
            Just m -> return m
            Nothing -> fail ("unsupported type in crucible_fresh_var: " ++ show (L.ppType lty))
  mty <- liftIO $ logicTypeOfActual dl sc lty'
  case mty of
    Just ty -> liftIO $ scFreshGlobal sc name ty >>= mkTypedTerm sc
    Nothing -> fail $ "Unsupported type in crucible_fresh_var: " ++ show (L.ppType lty)


crucible_alloc :: BuiltinContext
               -> Options
               -> L.Type
               -> CrucibleSetup SetupValue
crucible_alloc bic _opt lty = do
  cctx <- getCrucibleContext bic
  let lc  = Crucible.llvmTypeCtx (ccLLVMContext cctx)
  let ?dl = TyCtx.llvmDataLayout lc
  let ?lc = lc
  memTy <- case TyCtx.liftMemType lty of
    Just m -> return m
    Nothing -> fail ("unsupported type in crucible_alloc: " ++ show (L.ppType lty))
  st <- get
  let n  = csVarCounter st
      spec  = csMethodSpec st
      spec' = spec{ csAllocations = Map.insert n memTy (csAllocations spec) }
  put st{ csVarCounter = nextAllocIndex n
        , csMethodSpec = spec'
        }
  return (SetupVar n)

crucible_fresh_pointer ::
  BuiltinContext ->
  Options        ->
  L.Type         ->
  CrucibleSetup SetupValue
crucible_fresh_pointer bic _opt lty = do
  cctx <- getCrucibleContext bic
  let lc  = Crucible.llvmTypeCtx (ccLLVMContext cctx)
  let ?dl = TyCtx.llvmDataLayout lc
  let ?lc = lc
  memTy <- case TyCtx.liftMemType lty of
    Just m -> return m
    Nothing -> fail ("unsupported type in crucible_fresh_pointer: " ++ show (L.ppType lty))
  st <- get
  let n  = csVarCounter st
      spec  = csMethodSpec st
      spec' = spec{ csFreshPointers = Map.insert n memTy (csFreshPointers spec) }
  put st{ csVarCounter = nextAllocIndex n
        , csMethodSpec = spec'
        }
  return (SetupVar n)

crucible_points_to ::
  BuiltinContext ->
  Options        ->
  SetupValue     ->
  SetupValue     ->
  CrucibleSetup ()
crucible_points_to bic _opt ptr val =
  do cc <- getCrucibleContext bic
     let ?lc = Crucible.llvmTypeCtx (ccLLVMContext cc)
     st <- get
     let rs = csResolvedState st
     if csPrePost st == PreState && testResolved ptr rs
       then fail "Multiple points-to preconditions on same pointer"
       else put st{ csResolvedState = markResolved ptr rs }
     let env = csAllocations (csMethodSpec st)
     ptrTy <- typeOfSetupValue cc env ptr
     lhsTy <- case ptrTy of
       Crucible.PtrType symTy ->
         case TyCtx.asMemType symTy of
           Just lhsTy -> return lhsTy
           Nothing -> fail $ "lhs not a valid pointer type: " ++ show ptrTy
       _ -> fail $ "lhs not a pointer type: " ++ show ptrTy
     let valenv = Map.union (csAllocations (csMethodSpec st))
                            (csFreshPointers (csMethodSpec st))
     valTy <- typeOfSetupValue cc valenv val
     checkMemTypeCompatibility lhsTy valTy
     addCondition (SetupCond_PointsTo ptr val)

crucible_equal ::
  BuiltinContext ->
  Options        ->
  SetupValue     ->
  SetupValue     ->
  CrucibleSetup ()
crucible_equal bic _opt val1 val2 =
  do cc <- getCrucibleContext bic
     st <- get
     let env = Map.union (csAllocations (csMethodSpec st))
                         (csFreshPointers (csMethodSpec st))
     ty1 <- typeOfSetupValue cc env val1
     ty2 <- typeOfSetupValue cc env val2
     checkMemTypeCompatibility ty1 ty2
     addCondition (SetupCond_Equal val1 val2)


crucible_execute_func :: BuiltinContext
                      -> Options
                      -> [SetupValue]
                      -> CrucibleSetup ()
crucible_execute_func bic _opt args = do
  cctx <- lift (io (readIORef (biCrucibleContext bic))) >>= maybe (fail "No Crucible LLVM module loaded") return
  st <- get
  let ?lc   = Crucible.llvmTypeCtx (ccLLVMContext cctx)
  let ?dl   = TyCtx.llvmDataLayout ?lc
  let cs    = csMethodSpec st
  let tps   = csArgs cs
  let spec  = csMethodSpec st
  case traverse TyCtx.liftType tps of
    Just tps' -> do
      let spec' = spec{ csArgBindings =
                          Map.fromList $
                            [ (i, (t,a))
                            | i <- [0..]
                            | a <- args
                            | t <- tps'
                            ]
                      }
      put st{ csPrePost = PostState
            , csMethodSpec = spec'
            }

    _ -> fail $ unlines ["Function signature not supported:", show (csArgs cs)]


crucible_return :: BuiltinContext
                -> Options
                -> SetupValue
                -> CrucibleSetup ()
crucible_return _bic _opt retval = do
  st <- get
  let spec = csMethodSpec st
  case csRetValue spec of
    Just _ -> fail "crucible_return: duplicate return value specification"
    Nothing -> put st{ csMethodSpec = spec{ csRetValue = Just retval } }
