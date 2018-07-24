{- |
Module      : SAWScript.CrucibleBuiltinsJVM
Description : crucible-jvm specific code
Maintainer  : sweirich@galois.com
Stability   : provisional
-}


{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE EmptyCase #-}


{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-local-binds #-}
{-# OPTIONS_GHC -fno-warn-unused-imports #-}


module SAWScript.CrucibleBuiltinsJVM
       (
         loadJavaClass           -- java_load_class: reads a class from the codebase
       , crucible_java_extract   -- 
       , crucible_java_cfg
       ) where

import           Control.Lens
import           Data.Map (Map,(!))
import qualified Data.Map as Map
import           Data.Foldable (toList)
import           System.IO
import           Control.Monad (forM_,unless)
import           Control.Monad.ST

-- parameterized-utils
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as Nonce

-- crucible/crucible-saw
import qualified Lang.Crucible.Backend.SAWCore         as CrucibleSAW
-- crucible/crucible
import qualified Lang.Crucible.CFG.Core                as Crucible
import qualified Lang.Crucible.Simulator.ExecutionTree as Crucible
import qualified Lang.Crucible.Simulator.GlobalState   as Crucible
import qualified Lang.Crucible.Simulator.RegMap        as Crucible
import qualified Lang.Crucible.Simulator.OverrideSim   as Crucible
import qualified Lang.Crucible.Analysis.Postdom        as Crucible

-- crucible/what4
import qualified What4.Config as W4
import qualified What4.Interface as W4

-- saw-core
import Verifier.SAW.SharedTerm(Term, SharedContext, mkSharedContext, scImplies, scAbstractExts)
import Verifier.SAW.TypedTerm(TypedTerm, mkTypedTerm)

-- saw-script
import SAWScript.Builtins(fixPos)
import SAWScript.Value
import SAWScript.Options(Options,simVerbose)
import SAWScript.Utils (findMethod, findField, lookupClass, handleException)
import SAWScript.CrucibleBuiltins(setupArg, setupArgs, getGlobalPair, runCFG)

-- jvm-verifier
import qualified Language.JVM.Common as J
import qualified Language.JVM.Parser as J
import qualified Verifier.Java.Codebase as J

-- crucible-jvm
import qualified Lang.Crucible.JVM.Translation as CJ

import Debug.Trace

-----------------------------------------------------------------------
-- This is actually shared with the old Java static simulator.
-- Including it here so that we can retire the 'JavaBuiltins.hs' module
-- in the future.

loadJavaClass :: BuiltinContext -> String -> IO J.Class
loadJavaClass bic =
  lookupClass (biJavaCodebase bic) fixPos . J.mkClassName . J.dotsToSlashes

-----------------------------------------------------------------------
-- | translate a given class (if it hasn't already been translated) and
-- add it to the class translation table
translateClass :: J.Class -> TopLevel ()
translateClass c = do
  let cn = J.className c
  transClassMap <- getClassTrans
  unless (Map.member cn transClassMap) $ do
       halloc <- getHandleAlloc
       ct <- io $ stToIO $ CJ.translateClass halloc c
       addClassTrans (J.className c) ct  

----

type Sym = CrucibleSAW.SAWCoreBackend Nonce.GlobalNonceGenerator

data CrucibleJavaContext =
  CrucibleJavaContext
  { _cjcClassTrans     :: Map J.ClassName CJ.ClassTranslation
  , _cjcBackend        :: Sym
  , _cjcJavaSimContext :: Crucible.SimContext (CrucibleSAW.SAWCruciblePersonality Sym) Sym CJ.JVM
  , _cjcJavaGlobals    :: Crucible.SymGlobalState Sym
  }

makeLenses ''CrucibleJavaContext



-- NOTE: unlike the LLVM version of this function, which is already provided with a
-- translated module, this function needs to first *translate* the JVM code to crucible and
-- then set up the context for symbolic simulation.
setupCrucibleJavaContext ::
   BuiltinContext -> Options -> J.Class ->
   (CrucibleJavaContext -> TopLevel a) ->
   TopLevel a
setupCrucibleJavaContext bic opts c action = do
  -- halloc :: HandleAllocator RealWorld
  halloc <- getHandleAlloc
  AIGProxy proxy <- getProxy
  -- access the class translation from the toplevel context     
  transClassMap <- getClassTrans 

  let transClass = transClassMap ! (J.className c)
  
  action =<< (io $ do   -- only the IO monad, nothing else
      let gen = Nonce.globalNonceGenerator
      let sc  = biSharedContext bic
      let cb  = biJavaCodebase bic
      let verbosity = simVerbose opts
      sym <- CrucibleSAW.newSAWCoreBackend proxy sc gen

      let cfg = W4.getConfiguration sym
      verbSetting <- W4.getOptionSetting W4.verbosity cfg
      _ <- W4.setOpt verbSetting (toInteger verbosity)
      

      -- set up the simulation context

      let ctx = transClass^.CJ.transContext
      let sm = CJ.symbolMap ctx
      let cm = CJ.cfgMap transClass
      let gm = CJ.staticTable ctx
            
      let bindings = Crucible.fnBindingsFromList (map (mkFunBinding . snd) (Map.toList sm)) where
            mkFunBinding (CJ.JVMHandleInfo m _) = do
              case Map.lookup (J.className c, J.methodKey m) cm of
                Just (CJ.MethodTranslation h (Crucible.SomeCFG g)) -> 
                  Crucible.FnBinding h (Crucible.UseCFG g (Crucible.postdomInfo g))
                Nothing  -> error "cannot find method!"
            

      let javaExtImpl :: Crucible.ExtensionImpl p sym ()
          javaExtImpl = Crucible.ExtensionImpl (\_sym _iTypes _logFn _f x -> case x of)
                                               (\x -> case x of)

      let jsimctx   = Crucible.initSimContext sym MapF.empty halloc stdout
                        bindings javaExtImpl CrucibleSAW.SAWCruciblePersonality

      -- initialize the dynamic class table (to just an empty map)
      let globals = Crucible.insertGlobal (CJ.dynamicClassTable ctx) Map.empty Crucible.emptyGlobals
      

      return
         CrucibleJavaContext{ _cjcClassTrans     = Map.singleton (J.className c) transClass
                            , _cjcBackend        = sym
                            , _cjcJavaSimContext = jsimctx
                            , _cjcJavaGlobals    = globals
                            }
      
             )


  
-- | Return the CFG for a particular method
-- If the class has not already been translated to a Crucible CFG, do so
crucible_java_cfg :: BuiltinContext -> Options -> J.Class -> String -> TopLevel SAW_CFG
crucible_java_cfg bic _opts c mname = do
  translateClass c
  ctm <- getClassTrans
  let cb = biJavaCodebase bic
  let cm = CJ.cfgMap (ctm ! J.className c)
  (mcls, meth) <- io $ findMethod cb fixPos mname c
  case Map.lookup (J.className mcls, J.methodKey meth) cm of
     Nothing  -> fail $ unwords ["method", show $ J.methodKey meth, "not found"]
     Just (CJ.MethodTranslation _ (Crucible.SomeCFG cfg)) -> return (JVM_CFG (Crucible.AnyCFG cfg))

crucible_java_extract :: BuiltinContext -> Options -> J.Class -> String -> TopLevel TypedTerm
crucible_java_extract bic opts c mname = do
  translateClass c
  let cb = biJavaCodebase bic
  let cn = J.className c
  (mcls, meth) <- io $ findMethod cb fixPos mname c
  setupCrucibleJavaContext bic opts c $ \cc -> do
     let ct = (cc^.cjcClassTrans) ! cn
     let cm = CJ.cfgMap ct 
     
     sc <- getSharedContext

     case Map.lookup (J.className mcls, J.methodKey meth) cm of
        Nothing  -> fail $ unwords ["method", show $ J.methodKey meth, "not found"]
        Just (CJ.MethodTranslation _ (Crucible.SomeCFG cfg)) -> do

          io $ extractFromJavaCFG opts sc cc (Crucible.AnyCFG cfg)


extractFromJavaCFG ::
   Options -> SharedContext -> CrucibleJavaContext -> Crucible.AnyCFG CJ.JVM -> IO TypedTerm
extractFromJavaCFG opts sc cc (Crucible.AnyCFG cfg) =
  do  let sym = cc^.cjcBackend
      let h   = Crucible.cfgHandle cfg
      (ecs, args) <- setupArgs sc sym h
      let simCtx  = cc^.cjcJavaSimContext
      let globals = cc^.cjcJavaGlobals
      
      traceIO $ "Running cfg "
      
      res  <- runCFG simCtx globals h cfg args
      
      case res of
        Crucible.FinishedResult _ pr -> do
            gp <- getGlobalPair opts pr
            t <- Crucible.asSymExpr
                   (gp^.Crucible.gpValue)
                   (CrucibleSAW.toSC sym)
                   (fail $ unwords ["Unexpected return type:", show (Crucible.regType (gp^.Crucible.gpValue))])
            t' <- scAbstractExts sc (toList ecs) t
            mkTypedTerm sc t'
        Crucible.AbortedResult _ _ar -> do
          fail $ unlines [ "Symbolic execution failed." ]
