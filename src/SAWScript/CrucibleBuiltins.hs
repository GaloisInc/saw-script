{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}


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
import Data.Foldable (toList)
import Data.IORef
import Data.String
import System.IO
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Map as Map
import qualified Data.LLVM.BitCode as L
--import qualified Text.LLVM.AST as L

import qualified Data.Parameterized.Nonce as Crucible
import qualified Lang.Crucible.Config as Crucible
import qualified Lang.Crucible.Core as Crucible
import qualified Lang.Crucible.FunctionHandle as Crucible
import qualified Lang.Crucible.Simulator.CallFns as Crucible
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible
import qualified Lang.Crucible.Simulator.MSSim as Crucible
import qualified Lang.Crucible.Simulator.RegMap as Crucible
import qualified Lang.Crucible.Simulator.SimError as Crucible
import qualified Lang.Crucible.LLVM as Crucible
import qualified Lang.Crucible.LLVM.Translation as Crucible
import qualified Lang.Crucible.Solver.SAWCoreBackend as Crucible
import qualified Data.Parameterized.TraversableFC as Ctx

import Verifier.SAW.TypedAST
import Verifier.SAW.SharedTerm

import SAWScript.Builtins
import SAWScript.Options
import SAWScript.TypedTerm
import SAWScript.TopLevel



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


load_crucible_llvm_module :: BuiltinContext -> Options -> String -> TopLevel ()
load_crucible_llvm_module bic _opts bc_file = do
  halloc <- getHandleAlloc
  let r = biCrucibleContext bic
  io (L.parseBitCodeFromFile bc_file) >>= \case
    Left err -> fail (L.formatError err)
    Right llvm_mod -> io $ do
      (ctx, mtrans) <- stToIO $ Crucible.translateModule halloc llvm_mod
      let gen = Crucible.globalNonceGenerator
      let sc  = biSharedContext bic
      sym <- Crucible.newSAWCoreBackend sc gen
      cfg <- Crucible.initialConfig 10 []
      let bindings = Crucible.fnBindingsFromList []
      let simctx   = Crucible.initSimContext sym Crucible.llvmIntrinsicTypes cfg halloc stdout
                        bindings 
      mem <- Crucible.initalizeMemory sym ctx llvm_mod
      let globals  = Crucible.llvmGlobals ctx mem

      let setupMem :: Crucible.OverrideSim Sym
                       (Crucible.RegEntry Sym Crucible.UnitType)
                       Crucible.EmptyCtx Crucible.UnitType (Crucible.RegValue Sym Crucible.UnitType)
          setupMem = do
             -- register the callable override functions
             _llvmctx' <- execStateT Crucible.register_llvm_overrides ctx

             -- initalize LLVM global variables
             _ <- case Crucible.initMemoryCFG mtrans of
                     Crucible.SomeCFG initCFG ->
                       Crucible.callCFG initCFG Crucible.emptyRegMap

             -- register all the functions defined in the LLVM module
             mapM_ Crucible.registerModuleFn $ Map.toList $ Crucible.cfgMap mtrans

      res <- Crucible.run simctx globals errorHandler Crucible.UnitRepr setupMem
      (globals',simctx') <-
          case res of
            Crucible.FinishedExecution st (Crucible.TotalRes gp) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.FinishedExecution st (Crucible.PartialRes _ gp _) -> return (gp^.Crucible.gpGlobals, st)
            Crucible.AbortedResult _ _ -> fail "Memory initialization failed!"
      writeIORef r $ Just
         CrucibleContext{ ccLLVMContext = ctx
                        , ccLLVMModuleTrans = mtrans
                        , ccBackend = sym
                        , ccSimContext = simctx'
                        , ccGlobals = globals'
                        }

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

extractFromCFG :: SharedContext -> CrucibleContext -> Crucible.AnyCFG -> IO (CrucibleContext, TypedTerm)
extractFromCFG sc cc (Crucible.AnyCFG cfg) = do
  let sym = ccBackend cc
  let h   = Crucible.cfgHandle cfg
  (ecs, args) <- setupArgs sc sym h
  res  <- Crucible.run (ccSimContext cc) (ccGlobals cc) errorHandler (Crucible.handleReturnType h)
             (Crucible.regValue <$> (Crucible.callCFG cfg args))
  case res of
    Crucible.FinishedExecution st pr -> do
        gp <- case pr of
                Crucible.TotalRes gp -> return gp
                Crucible.PartialRes _ gp _ -> do
                  putStrLn "Symbolic simulation failed along some paths!"
                  return gp
        let cc' = cc{ ccSimContext = st, ccGlobals = gp^.Crucible.gpGlobals }
        t <- Crucible.asSymExpr
                   (gp^.Crucible.gpValue)
                   (Crucible.toSC sym) 
                   (fail $ unwords ["Unexpected return type:", show (Crucible.regType (gp^.Crucible.gpValue))])
        t' <- scAbstractExts sc (toList ecs) t
        tt <- mkTypedTerm sc t'
        return (cc', tt)
    Crucible.AbortedResult _ _ -> fail "Symbolic execution failed on all paths!"


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
           (cc', tt) <- extractFromCFG sc cc cfg
           writeIORef r (Just cc')
           return tt

load_llvm_cfg :: BuiltinContext -> Options -> String -> TopLevel Crucible.AnyCFG
load_llvm_cfg bic _opts fn_name = do
  let r = biCrucibleContext bic
  io (readIORef r) >>= \case
    Nothing -> fail "No Crucible LLVM module loaded"
    Just cc -> 
      case Map.lookup (fromString fn_name) (Crucible.cfgMap (ccLLVMModuleTrans cc)) of
        Nothing  -> fail $ unwords ["function", fn_name, "not found"]
        Just cfg -> return cfg
