{- |
Module      : SAWCentral.Crucible.JVM.BuiltinsJVM
Description : crucible-jvm specific code
Maintainer  : sweirich@galois.com
Stability   : provisional
-}


{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE PackageImports #-}


{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}


module SAWCentral.Crucible.JVM.BuiltinsJVM
       (
         loadJavaClass           -- java_load_class: reads a class from the codebase
       , prepareClassTopLevel
       , jvm_extract   --
       ) where

import           Data.List (isPrefixOf)
import           Control.Lens
import           Data.Text (Text)
import qualified Data.Text as Text
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
import SAWCore.SharedTerm(Term, SharedContext, mkSharedContext, scImplies)

-- cryptol-saw-core
import CryptolSAWCore.TypedTerm (TypedTerm(..), abstractTypedExts, TypedTermType(..))

-- saw-core-what4
import SAWCoreWhat4.ReturnTrip

-- saw-script
import SAWCentral.Value
import SAWCentral.Options(Options,simVerbose)
import SAWCentral.Crucible.Common
import SAWCentral.Crucible.LLVM.Builtins (setupArg, setupArgs, getGlobalPair, runCFG, baseCryptolType)

-- jvm-parser
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J

import qualified SAWCentral.Utils as J
import qualified Lang.JVM.Codebase as JCB

-- crucible-jvm
import           Lang.Crucible.JVM (IsCodebase(..))
import qualified Lang.Crucible.JVM as CJ

import Debug.Trace

-----------------------------------------------------------------------
-- | Make sure the class is in the database and allocate handles for its
-- methods and static fields
--
loadJavaClass :: Text -> TopLevel J.Class
loadJavaClass str = do
  -- XXX fix prepareClassTopLevel to return c so we don't have to look
  -- it up twice
  cb <- getJavaCodebase
  c <- io $ findClass cb (Text.unpack str)
  prepareClassTopLevel str
  return c

-----------------------------------------------------------------------
-- | Allocate the method handles/global static variables for the given
-- class and add them to the current translation context
prepareClassTopLevel :: Text -> TopLevel ()
prepareClassTopLevel str = do

   cb <- getJavaCodebase

   -- get class from codebase
   c <- io $ findClass cb (Text.unpack str)

   -- get current ctx
   ctx0 <- getJVMTrans

   -- make sure that we haven't already processed this class
   unless (Map.member (J.className c) (CJ.classTable ctx0)) $ do

     -- add handles/global variables for this class
     halloc <- getHandleAlloc
     ctx <- io $ execStateT (CJ.extendJVMContext halloc c) ctx0

     -- update ctx
     putJVMTrans ctx


-----------------------------------------------------------------------


-- | Extract a JVM method to saw-core
--
jvm_extract :: J.Class -> Text -> TopLevel TypedTerm
jvm_extract c mname = do
  sc <- getSharedContext
  cb <- getJavaCodebase
  opts <- getOptions
  pathSatSolver <- gets rwPathSatSolver
  let verbosity = simVerbose opts
  let gen       = Nonce.globalNonceGenerator


  traceM $ "extracting " ++ Text.unpack mname
  (mcls, meth) <- io $ CJ.findMethod cb (Text.unpack mname) c
  when (not (J.methodIsStatic meth)) $ do
       fail $ unlines [ "Crucible can only extract static methods" ]

  let className = J.className c

  -- allocate all of the handles/static vars that are directly referenced by
  -- this class
  let refs = CJ.initClasses ++ Set.toList (CJ.classRefs c)
  mapM_ (prepareClassTopLevel . Text.pack . J.unClassName) refs

  halloc <- getHandleAlloc
  ctx <- getJVMTrans

  io $ do -- only the IO monad, nothing else
          sym <- newSAWCoreExprBuilder sc False
          SomeOnlineBackend bak <- newSAWCoreBackend pathSatSolver sym
          st  <- sawCoreState sym
          CJ.setSimulatorVerbosity verbosity sym

          (CJ.JVMHandleInfo _m2 h) <- CJ.findMethodHandle ctx mcls meth

          (ecs, args) <- setupArgs sc sym h

          res <- CJ.runMethodHandle bak SAWCruciblePersonality halloc
                     ctx verbosity className h args

          case res of
            Crucible.FinishedResult _ pr -> do
              gp <- getGlobalPair opts pr
              let regval = gp^.Crucible.gpValue
              let regty = Crucible.regType regval
              let failure :: forall a. IO a
                  failure = fail $ unwords ["Unexpected return type:", show regty]
              t <- Crucible.asSymExpr regval (toSC sym st) failure
              cty <-
                case Crucible.asBaseType regty of
                  Crucible.NotBaseType -> failure
                  Crucible.AsBaseType bt ->
                    case baseCryptolType bt of
                      Nothing -> failure
                      Just cty -> return cty
              let tt = TypedTerm (TypedTermSchema (Cryptol.tMono cty)) t
              abstractTypedExts sc (toList ecs) tt
            Crucible.AbortedResult _ _ar -> do
              fail $ unlines [ "Symbolic execution failed." ]
            Crucible.TimeoutResult _cxt -> do
              fail $ unlines [ "Symbolic execution timed out." ]
