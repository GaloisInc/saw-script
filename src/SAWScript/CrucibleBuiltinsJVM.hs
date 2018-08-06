{- |
Module      : SAWScript.CrucibleBuiltinsJVM
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


module SAWScript.CrucibleBuiltinsJVM
       (
         loadJavaClass           -- java_load_class: reads a class from the codebase
       , translateClassTopLevel
       , translateClassRefs
       , crucible_java_extract   -- 
       , crucible_java_cfg
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
import qualified "jvm-verifier" Verifier.Java.Codebase as J

-- crucible-jvm
import qualified Lang.Crucible.JVM.Translation as CJ
import qualified Lang.Crucible.JVM.ClassRefs as CJ

import Debug.Trace

-----------------------------------------------------------------------
-- This is actually shared with the old Java static simulator.
-- Including it here so that we can retire the 'JavaBuiltins.hs' module
-- in the future.

loadJavaClass :: BuiltinContext -> String -> TopLevel J.Class
loadJavaClass bic str = do
  c <- io $ (lookupClass (biJavaCodebase bic) fixPos . J.mkClassName . J.dotsToSlashes) str
  prepareClassToplevel bic str
--  jvmTrans <- getJVMTrans
--  let ctx = CJ.transContext jvmTrans
--  addJVMTrans (CJ.JVMTranslation Map.empty (CJ.addToClassTable c ctx))
  
  return c

-----------------------------------------------------------------------
-- Allocate the method handles/global static variables for the given
-- class and add them to the current translation context
prepareClassToplevel :: BuiltinContext -> String -> TopLevel ()
prepareClassToplevel bic str = do
  
   -- get class from codebase
   c <- io $ (lookupClass (biJavaCodebase bic) fixPos . J.mkClassName . J.dotsToSlashes) str

   -- get current ctx
   jvmTrans <- getJVMTrans
   let ctx0 = CJ.transContext jvmTrans

   -- make sure that we haven't already processed this class
   unless (Map.member (J.className c) (CJ.classTable ctx0)) $ do 

     -- add handles/global variables for this class
     halloc <- getHandleAlloc
     ctx <- io $ stToIO $ CJ.extendJVMContext halloc ctx0 c 
   
     -- update ctx
     addJVMTrans (CJ.JVMTranslation Map.empty (CJ.addToClassTable c ctx))


-----------------------------------------------------------------------
-- | translate a given class (if it hasn't already been translated) and
-- add it to the class translation table
translateClassTopLevel :: J.Class -> TopLevel ()
translateClassTopLevel c = do
  let cn = J.className c
  jvmTrans <- getJVMTrans
  let transClassMap = CJ.translatedClasses jvmTrans
  unless (Map.member cn transClassMap) $ do
       halloc <- getHandleAlloc
       newjvm <- io $ stToIO $ CJ.translateClass halloc (CJ.transContext jvmTrans) c
       addJVMTrans newjvm  

----
translateClassRefs ::  BuiltinContext -> String -> TopLevel ()
translateClassRefs bic str = do
       cns <- go Set.empty cn0
       traceM $ show cns
       cs  <- io $ mapM (lookupClass (biJavaCodebase bic) fixPos) (Set.toList cns)
       halloc <- getHandleAlloc
       jvmTrans <- getJVMTrans
       
       newjvm <- io $ stToIO $ CJ.translateClasses halloc
         (CJ.transContext jvmTrans) cs
       addJVMTrans newjvm
  where
    cn0 = (J.mkClassName . J.dotsToSlashes) str

    
    go found cn =
      if (cn `Set.member` found
          || ("java/util/" `isPrefixOf` J.unClassName cn)
          || ("java/math/" `isPrefixOf` J.unClassName cn)
          || ("java/io/"   `isPrefixOf` J.unClassName cn)
          || ("java/nio/"  `isPrefixOf` J.unClassName cn)
          || ("["          `isPrefixOf` J.unClassName cn)
          || ("java/time/" `isPrefixOf` J.unClassName cn)
          || ("sun/"       `isPrefixOf` J.unClassName cn)
          || ("java/security/" `isPrefixOf` J.unClassName cn)
          || ("java/text/"     `isPrefixOf` J.unClassName cn)
          || ("java/lang/reflect/"     `isPrefixOf` J.unClassName cn)
          || ("java/lang/ref/" `isPrefixOf` J.unClassName cn)
          || ("java/net/"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/Thread"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/CharSequence"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/ClassLoader"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/Character"    `isPrefixOf` J.unClassName cn)
          || ("java/lang/ConditionalSpecialCasing"  `isPrefixOf` J.unClassName cn)
          || cn `elem`
           [   J.mkClassName "java/lang/Object"
             , J.mkClassName "java/lang/Class"
             , J.mkClassName "java/lang/Package"
             , J.mkClassName "java/lang/SecurityManager"
             , J.mkClassName "java/lang/Shutdown"
             , J.mkClassName "java/lang/Process"
             , J.mkClassName "java/lang/Runtime"
             , J.mkClassName "java/lang/RuntimePermission"
             , J.mkClassName "java/lang/StackTraceElement"
             , J.mkClassName "java/lang/ProcessEnvironment"
             , J.mkClassName "java/lang/ProcessBuilder"
             , J.mkClassName "java/lang/Thread"
             , J.mkClassName "java/lang/ThreadLocal"
             , J.mkClassName "java/lang/ApplicationShutdownHooks"
             , J.mkClassName "java/lang/invoke/SerializedLambda"
             , J.mkClassName "java/lang/System$2"
             , J.mkClassName "java/lang/AbstractStringBuilder"
             , J.mkClassName "java/lang/StringBuilder"
           ])
        then return found
        else do
         traceM $ "go " ++ J.unClassName cn
         
         c <- io $ lookupClass (biJavaCodebase bic) fixPos cn
         foldM go
           (Set.insert cn found)
           (Set.toList (CJ.classRefs c))


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
  jvmTrans <- getJVMTrans
  
  let transClassMap = CJ.translatedClasses jvmTrans
  
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

      let ctx = CJ.transContext jvmTrans
            
      let bindings = CJ.mkBindings ctx transClassMap 

      let javaExtImpl :: Crucible.ExtensionImpl p sym CJ.JVM
          javaExtImpl = Crucible.ExtensionImpl (\_sym _iTypes _logFn _f x -> case x of)
                                               (\x -> case x of)

      let jsimctx   = Crucible.initSimContext sym MapF.empty halloc stdout
                        bindings javaExtImpl CrucibleSAW.SAWCruciblePersonality

      -- initialize the dynamic class table (to just an empty map)
      let globals = Crucible.insertGlobal (CJ.dynamicClassTable ctx)
                                           Map.empty Crucible.emptyGlobals
      

      return
         CrucibleJavaContext{ _cjcClassTrans     = transClassMap
                            , _cjcBackend        = sym
                            , _cjcJavaSimContext = jsimctx
                            , _cjcJavaGlobals    = globals
                            }
      
             )


  
-- | Return the CFG for a particular method
-- If the class has not already been translated to a Crucible CFG, do so
crucible_java_cfg :: BuiltinContext -> Options -> J.Class -> String -> TopLevel SAW_CFG
crucible_java_cfg bic _opts c mname = do
  translateClassTopLevel c
  jvmt <- getJVMTrans
  let ctm = CJ.translatedClasses jvmt
  let cb = biJavaCodebase bic
  let cm = CJ.cfgMap (ctm ! J.className c)
  (mcls, meth) <- io $ findMethod cb fixPos mname c
  case Map.lookup (J.className mcls, J.methodKey meth) cm of
     Nothing  -> fail $ unwords ["method", show $ J.methodKey meth, "not found"]
     Just (CJ.MethodTranslation _ (Crucible.SomeCFG cfg)) -> return (JVM_CFG (Crucible.AnyCFG cfg))



{-
crucible_java_extract :: BuiltinContext -> Options -> J.Class -> String -> TopLevel TypedTerm
crucible_java_extract bic opts c mname = do
  translateClassTopLevel c
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
-}

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

---------------------------------------------------------------------------------

crucible_java_extract :: BuiltinContext -> Options -> J.Class -> String -> TopLevel TypedTerm
crucible_java_extract bic opts c mname = do
  traceM $ "extracting " ++ mname
  
  let refs = Set.toList (CJ.classRefs c)

  traceM $ "refs are " ++ show refs

  -- allocate all of the handles/static vars that we could need
  mapM_ (prepareClassToplevel bic . J.unClassName) refs

  jvmTrans <- getJVMTrans
  let ctx = CJ.transContext jvmTrans
  sc <- getSharedContext
  
  -- find the handle for the method to extract
  (mcls, meth) <- io $ findMethod (biJavaCodebase bic) fixPos mname c

  when (not (J.methodIsStatic meth)) $ do
    fail $ unlines [ "Crucible can only extract static methods" ]
  
  case Map.lookup (J.className mcls, J.methodKey meth) (CJ.methodHandles ctx) of
    Just (CJ.JVMHandleInfo m2 h) -> do
      
      traceM $ "found handle:" ++ show m2 ++ "\n" ++ show h ++ "\n"
      
      setupDelayedCrucibleJavaContext bic opts $ \cc -> io $ do
        
        traceM $ "setup simcontext "
        
        let sym     = cc^.cjcBackend
        let simCtx  = cc^.cjcJavaSimContext
        let globals = cc^.cjcJavaGlobals
        
        (ecs, args) <- setupArgs sc sym h
      
        traceIO $ "Running delayed cfg "
        let simSt = Crucible.initSimState simCtx globals Crucible.defaultAbortHandler  

        res  <- Crucible.executeCrucible simSt $
                Crucible.runOverrideSim (Crucible.handleReturnType h)
                (Crucible.regValue <$> (Crucible.callFnVal (Crucible.HandleFnVal h) args))
      
        case res of
          Crucible.FinishedResult _ pr -> do
            gp <- getGlobalPair opts pr
            t <- Crucible.asSymExpr
                   (gp^.Crucible.gpValue)
                   (CrucibleSAW.toSC sym)
                   (fail $ unwords ["Unexpected return type:",
                                    show (Crucible.regType (gp^.Crucible.gpValue))])
            t' <- scAbstractExts sc (toList ecs) t
            mkTypedTerm sc t'
          Crucible.AbortedResult _ _ar -> do
            fail $ unlines [ "Symbolic execution failed." ]

    Nothing -> error $ "BUG: cannot find handle for " ++ J.unClassName (J.className mcls) ++ "/" ++ J.methodName meth


-- NOTE: unlike the LLVM version of this function, which is already provided with a
-- translated module, this function needs to first *translate* the JVM code to crucible and
-- then set up the context for symbolic simulation.
setupDelayedCrucibleJavaContext ::
   BuiltinContext -> Options -> 
   (CrucibleJavaContext -> TopLevel a) ->
   TopLevel a
setupDelayedCrucibleJavaContext bic opts action = do
  -- halloc :: HandleAllocator RealWorld
  halloc <- getHandleAlloc
  AIGProxy proxy <- getProxy

  jvmTrans <- getJVMTrans
  let ctx = CJ.transContext jvmTrans

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
      let bindings = CJ.mkDelayedBindings ctx

      let javaExtImpl :: Crucible.ExtensionImpl p sym CJ.JVM
          javaExtImpl = Crucible.ExtensionImpl (\_sym _iTypes _logFn _f x -> case x of)
                                               (\x -> case x of)

      let jsimctx   = Crucible.initSimContext sym MapF.empty halloc stdout
                        bindings javaExtImpl CrucibleSAW.SAWCruciblePersonality

      -- initialize the dynamic class table (to just an empty map)
      let globals = Crucible.insertGlobal (CJ.dynamicClassTable ctx)
                                           Map.empty Crucible.emptyGlobals

      return
         CrucibleJavaContext{ _cjcClassTrans     = CJ.translatedClasses jvmTrans
                            , _cjcBackend        = sym
                            , _cjcJavaSimContext = jsimctx
                            , _cjcJavaGlobals    = globals
                            }
      
             )
