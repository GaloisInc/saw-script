{- |
Module      : SAWScript.Crucible.JVM.BuiltinsJVM
Description : crucible-jvm specific code
Maintainer  : sweirich@galois.com
Stability   : provisional
-}


{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PackageImports #-}


{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}


module SAWScript.Crucible.JVM.BuiltinsJVM
       (
         loadJavaClass           -- java_load_class: reads a class from the codebase
       , prepareClassTopLevel
       , crucible_java_extract   --
       ) where

import           Data.List (isPrefixOf)
import           Control.Lens
import           Data.Map (Map,(!))
import qualified Data.Map as Map
import qualified Data.Set as Set
import           Data.Foldable (toList)
import           System.IO
import           Control.Monad (forM_,unless,when,foldM)
import           Control.Monad.ST
import           Control.Monad.State.Strict

-- parameterized-utils
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as Nonce

-- crucible/crucible-saw
import qualified Lang.Crucible.Backend.SAWCore         as CrucibleSAW
-- crucible/crucible
import qualified Lang.Crucible.FunctionHandle          as Crucible
import qualified Lang.Crucible.Simulator.Operations    as Crucible
import qualified Lang.Crucible.Simulator.EvalStmt      as Crucible

import qualified Lang.Crucible.CFG.Core                as Crucible
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible
import qualified Lang.Crucible.Simulator.GlobalState   as Crucible
import qualified Lang.Crucible.Simulator.RegMap        as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim   as Crucible
import qualified Lang.Crucible.Analysis.Postdom        as Crucible

-- cryptol
import qualified Cryptol.TypeCheck.Type as Cryptol

-- crucible/what4
import qualified What4.Expr as W4
import qualified What4.Config as W4
import qualified What4.Interface as W4
import qualified What4.Solver.Yices as Yices

-- saw-core
import Verifier.SAW.SharedTerm(Term, SharedContext, mkSharedContext, scImplies, scAbstractExts)

-- cryptol-saw-core
import Verifier.SAW.TypedTerm(TypedTerm(..))

-- saw-script
import SAWScript.Builtins(fixPos)
import SAWScript.Value
import SAWScript.Options(Options,simVerbose)
import SAWScript.Crucible.LLVM.Builtins (setupArg, setupArgs, getGlobalPair, runCFG, baseCryptolType)

-- jvm-verifier
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J
import qualified SAWScript.Utils as J
import qualified "jvm-verifier" Verifier.Java.Codebase as JCB

-- crucible-jvm
import           Lang.Crucible.JVM (IsCodebase(..))
import qualified Lang.Crucible.JVM as CJ

import Debug.Trace

--
-- | Use the Codebase implementation from the old Java static simulator
--
instance IsCodebase JCB.Codebase where
  lookupClass cb = J.lookupClass cb fixPos
  findMethod  cb = J.findMethod  cb fixPos

-----------------------------------------------------------------------
-- | Make sure the class is in the database and allocate handles for its
-- methods and static fields
--
loadJavaClass :: BuiltinContext -> String -> TopLevel J.Class
loadJavaClass bic str = do
  c <- io $ findClass (biJavaCodebase bic) str
  prepareClassTopLevel bic str
  return c

-----------------------------------------------------------------------
-- | Allocate the method handles/global static variables for the given
-- class and add them to the current translation context
prepareClassTopLevel :: BuiltinContext -> String -> TopLevel ()
prepareClassTopLevel bic str = do

   -- get class from codebase
   c <- io $ findClass (biJavaCodebase bic) str

   -- get current ctx
   ctx0 <- getJVMTrans

   -- make sure that we haven't already processed this class
   unless (Map.member (J.className c) (CJ.classTable ctx0)) $ do

     -- add handles/global variables for this class
     halloc <- getHandleAlloc
     ctx <- io $ execStateT (CJ.extendJVMContext halloc c) ctx0

     -- update ctx
     addJVMTrans ctx


-----------------------------------------------------------------------


-- | Extract a JVM method to saw-core
--
crucible_java_extract :: BuiltinContext -> Options -> J.Class -> String -> TopLevel TypedTerm
crucible_java_extract bic opts c mname = do
  let sc        = biSharedContext bic
  let cb        = biJavaCodebase bic
  let verbosity = simVerbose opts
  let gen       = Nonce.globalNonceGenerator


  traceM $ "extracting " ++ mname
  (mcls, meth) <- io $ CJ.findMethod cb mname c
  when (not (J.methodIsStatic meth)) $ do
       fail $ unlines [ "Crucible can only extract static methods" ]

  let className = J.className c

  -- allocate all of the handles/static vars that are directly referenced by
  -- this class
  let refs = CJ.initClasses ++ Set.toList (CJ.classRefs c)
  mapM_ (prepareClassTopLevel bic . J.unClassName) refs

  halloc <- getHandleAlloc
  ctx <- getJVMTrans

  io $ do -- only the IO monad, nothing else
          sym <- CrucibleSAW.newSAWCoreBackend W4.FloatRealRepr sc gen
          CJ.setSimulatorVerbosity verbosity sym

          (CJ.JVMHandleInfo _m2 h) <- CJ.findMethodHandle ctx mcls meth

          (ecs, args) <- setupArgs sc sym h

          res <- CJ.runMethodHandle sym CrucibleSAW.SAWCruciblePersonality halloc
                     ctx verbosity className h args

          case res of
            Crucible.FinishedResult _ pr -> do
              gp <- getGlobalPair opts pr
              let regval = gp^.Crucible.gpValue
              let regty = Crucible.regType regval
              let failure = fail $ unwords ["Unexpected return type:", show regty]
              t <- Crucible.asSymExpr regval (CrucibleSAW.toSC sym) failure
              cty <-
                case Crucible.asBaseType regty of
                  Crucible.NotBaseType -> failure
                  Crucible.AsBaseType bt ->
                    case baseCryptolType bt of
                      Nothing -> failure
                      Just cty -> return cty
              t' <- scAbstractExts sc (map snd (toList ecs)) t
              let cty' = foldr Cryptol.tFun cty (map fst (toList ecs))
              return $ TypedTerm (Cryptol.tMono cty') t'
            Crucible.AbortedResult _ _ar -> do
              fail $ unlines [ "Symbolic execution failed." ]
            Crucible.TimeoutResult _cxt -> do
              fail $ unlines [ "Symbolic execution timed out." ]
