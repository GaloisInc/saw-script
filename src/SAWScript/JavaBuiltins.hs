{- |
Module      : SAWScript.JavaBuiltins
Description : Implementations of Java-related SAW-Script primitives.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}

module SAWScript.JavaBuiltins where

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (empty)
#endif
import Control.Lens
import Control.Monad.State
import Control.Monad.Trans.Except
import Data.List (partition)
import Data.Maybe (mapMaybe)
import Data.IORef
import qualified Data.Map as Map
import Data.Time.Clock
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import Language.JVM.Common

import Verifier.Java.Codebase hiding (lookupClass)
import Verifier.Java.Simulator as JSS hiding (lookupClass)
import Verifier.Java.SAWBackend

import Verifier.SAW.Cryptol (importType, emptyEnv, exportFirstOrderValue)
import Verifier.SAW.Recognizer
import Verifier.SAW.FiniteValue (FirstOrderValue)
import Verifier.SAW.SCTypeCheck hiding (TypedTerm)
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm
import Verifier.SAW.CryptolEnv (schemaNoUser)

import qualified SAWScript.CongruenceClosure as CC

import SAWScript.JavaExpr
import SAWScript.JavaMethodSpec
import SAWScript.JavaMethodSpecIR
import SAWScript.JavaUtils

import SAWScript.Builtins
import SAWScript.Options
import SAWScript.Position (Pos(..), renderDoc)
import SAWScript.Proof
import SAWScript.Utils
import SAWScript.Value as SS

import qualified Cryptol.Eval.Monad as Cryptol (runEval)
import qualified Cryptol.Eval.Value as Cryptol (ppValue)
import qualified Cryptol.Eval.Concrete.Value as Cryptol (Concrete(..))
import qualified Cryptol.TypeCheck.AST as Cryptol
import qualified Cryptol.Utils.PP as Cryptol (pretty)

loadJavaClass :: BuiltinContext -> String -> IO Class
loadJavaClass bic =
  lookupClass (biJavaCodebase bic) fixPos . mkClassName . dotsToSlashes

getActualArgTypes :: JavaSetupState -> Either String [JavaActualType]
getActualArgTypes s = mapM getActualType declaredTypes
  where
    declaredTypes = zip [0..] (methodParameterTypes meth)
    ir = jsSpec s
    meth = specMethod ir
    getActualType (n, ty) = do
      let i = localIndexOfParameter meth n
          atys = [ aty | (CC.Term (Local _ i' _), aty) <-
                         Map.toList (specActualTypeMap ir), i == i' ]
      case atys of
        [] | isPrimitiveType ty -> Right (PrimitiveType ty)
           | otherwise ->
             Left $ "No declared type for non-scalar parameter " ++ show n
        [aty] -> Right aty
        _ -> Left $ "More than one actual type given for parameter " ++ show n

type Assign = (JavaExpr, TypedTerm)

symexecJava :: BuiltinContext
            -> Options
            -> Class
            -> String
            -> [(String, TypedTerm)]
            -> [String]
            -> Bool
            -> TopLevel TypedTerm
symexecJava bic opts cls mname inputs outputs satBranches = do
  let cb = biJavaCodebase bic
      pos = fixPos
      jsc = biSharedContext bic
      fl = defaultSimFlags { alwaysBitBlastBranchTerms = True
                           , satAtBranches = satBranches
                           }
  (_mcls, meth) <- io $ findMethod cb pos mname cls
  -- TODO: should we use mcls anywhere below?
  let mkAssign (s, tm) = do
        e <- parseJavaExpr' cb cls meth s
        return (e, tm)
      multDefErr i = error $ "Multiple terms given for " ++ ordinal (i + 1) ++
                             " argument in method " ++ methodName meth
      noDefErr i = fail $ "No binding for " ++ ordinal (i + 1) ++
                          " argument in method " ++ methodName meth
      pidx = fromIntegral . localIndexOfParameter meth
  withSAWBackend Nothing $ \sbe -> io $ do
    runSimulator cb sbe defaultSEH (Just fl) $ do
      setVerbosity (simVerbose opts)
      assigns <- mapM mkAssign inputs
      let (argAssigns, otherAssigns) = partition (isArg meth . fst) assigns
          argMap = Map.fromListWithKey (\i _ _ -> multDefErr i)
                   [ (idx, tm) | (CC.Term (Local _ idx _), tm) <- argAssigns ]
      argTms <- forM [0..maxArg meth] $ \i ->
                  maybe (noDefErr i) return $ Map.lookup (pidx i) argMap
      actualArgTys <- liftIO $ mapM (scTypeOf jsc . ttTerm) argTms
      let expectedArgTys = methodParameterTypes meth
      forM_ (zip actualArgTys expectedArgTys) $ \ (aty, ety) -> do
        comp <- liftIO $ termTypeCompatible jsc aty ety
        unless comp $ fail $
          "Passing value of type " ++ show aty ++
          " to argument expected to be of type " ++ show ety ++ "."
      args <- mapM (uncurry (valueOfTerm jsc)) (zip expectedArgTys argTms)
      mapM_ (uncurry (writeJavaTerm jsc)) otherAssigns
      allArgs <- case methodIsStatic meth of
                   True -> return args
                   False -> do
                     this <- createInstance (className cls) Nothing
                     return (RValue this : args)
      let localMap = setupLocals allArgs
      mp <- execMethod (className cls) (methodKey meth) localMap
      ps <- case mp of
              Nothing -> fail "No paths returned from execMethod"
              Just (ps, _) -> return ps
      outtms <- forM outputs $ \ostr -> do
        case ostr of
          "$safety" -> return (ps ^. pathAssertions)
          _-> do
            e <- parseJavaExpr' cb cls meth ostr
            readJavaTerm jsc (Just localMap) ps e
      let bundle tms = case tms of
                         [t] -> return t
                         _ -> scTuple jsc tms
      liftIO (mkTypedTerm jsc =<< bundle outtms)

extractJava :: BuiltinContext -> Options -> Class -> String
            -> JavaSetup ()
            -> TopLevel TypedTerm
extractJava bic opts cls mname setup = do
  let cb = biJavaCodebase bic
      pos = fixPos
      jsc = biSharedContext bic
  argsRef <- io $ newIORef []
  withSAWBackend (Just argsRef) $ \sbe -> do
    setupRes <- runJavaSetup pos cb cls mname setup
    let fl = defaultSimFlags { alwaysBitBlastBranchTerms =
                                 jsSatBranches setupRes }
        meth = specMethod (jsSpec setupRes)
    io $ runSimulator cb sbe defaultSEH (Just fl) $ do
      setVerbosity (simVerbose opts)
      argTypes <- either fail return (getActualArgTypes setupRes)
      args <- mapM (freshJavaVal (Just argsRef) jsc) argTypes
      -- TODO: support initializing other state elements
      rslt <- case methodIsStatic meth of
                True -> execStaticMethod (className cls) (methodKey meth) args
                False -> do
                  ~(RValue this) <- freshJavaVal (Just argsRef) jsc (ClassInstance cls)
                  execInstanceMethod (className cls) (methodKey meth) this args
      dt <- case (rslt, methodReturnType meth) of
              (Nothing, _) -> fail $ "No return value from " ++ methodName meth
              (_, Nothing) -> fail $ "Return value from void method " ++ methodName meth
              (Just v, Just tp) -> termOfValueSim jsc tp v
      liftIO $ do
        let sc = biSharedContext bic
        argBinds <- reverse <$> readIORef argsRef
        let exts = mapMaybe asExtCns argBinds
        -- TODO: group argBinds according to the declared types
        scAbstractExts jsc exts dt >>= mkTypedTerm sc

withSAWBackend :: Maybe (IORef [Term])
               -> (Backend SharedContext -> TopLevel a)
               -> TopLevel a
withSAWBackend argsRef a = do
  sc <- getSharedContext
  AIGProxy proxy <- getProxy
  io (sawBackend sc argsRef proxy) >>= a

runJavaSetup :: Pos -> Codebase -> Class -> String
             -> StateT JavaSetupState TopLevel a
             -> TopLevel JavaSetupState
runJavaSetup pos cb cls mname setup = do
  sc <- getSharedContext
  ms <- io $ initMethodSpec pos cb cls mname
  let setupState = JavaSetupState {
                     jsSpec = ms
                   , jsContext = sc
                   , jsTactic = Skip
                   , jsSimulate = True
                   , jsSatBranches = False
                   }
  execStateT setup setupState

verifyJava :: BuiltinContext -> Options -> Class -> String
           -> [JavaMethodSpecIR]
           -> JavaSetup ()
           -> TopLevel JavaMethodSpecIR
verifyJava bic opts cls mname overrides setup = do
  startTime <- io $ getCurrentTime
  let pos = fixPos -- TODO
      cb = biJavaCodebase bic
      bsc = biSharedContext bic
      jsc = bsc
  setupRes <- runJavaSetup pos cb cls mname setup
  let ms = jsSpec setupRes
      vp = VerifyParams {
             vpCode = cb
           , vpContext = jsc
           , vpOpts = opts
           , vpSpec = ms
           , vpOver = overrides
           }
  when (jsSimulate setupRes) $ do
    let overrideText =
          case overrides of
            [] -> ""
            irs -> " (overriding " ++ show (map renderName irs) ++ ")"
        renderName ir = unClassName (className (specMethodClass ir)) ++ "." ++
                        methodName (specMethod ir)
        configs = [ (bs, cl)
                  | bs <- {- concat $ Map.elems $ -} [specBehaviors ms]
                  , cl <- bsRefEquivClasses bs
                  ]
        fl = defaultSimFlags { alwaysBitBlastBranchTerms = True
                             , satAtBranches = jsSatBranches setupRes
                             }
    printOutLnTop Debug $ "Starting verification of " ++ specName ms
    ro <- getTopLevelRO
    rw <- getTopLevelRW
    forM_ configs $ \(bs,cl) -> withSAWBackend Nothing $ \sbe -> io $ do
      liftIO $ bsCheckAliasTypes pos bs
      liftIO $ printOutLn opts Debug $ "Executing " ++ specName ms ++
                   " at PC " ++ show (bsLoc bs) ++ "."
      -- runDefSimulator cb sbe $ do
      runSimulator cb sbe defaultSEH (Just fl) $ do
        setVerbosity (simVerbose opts)
        let prover script vs n g = do
              let exts = getAllExts g
              gprop <- io $ scGeneralizeExts jsc exts =<< scEqTrue jsc g
              io $ doExtraChecks opts bsc gprop
              let goal = ProofGoal n "vc" (vsVCName vs) (Prop gprop)
              r <- evalStateT script (startProof goal)
              case r of
                SS.Unsat _ -> liftIO $ printOutLn opts Debug "Valid."
                SS.SatMulti _ vals ->
                       io $ showCexResults opts jsc (rwPPOpts rw) ms vs exts vals
        let ovds = vpOver vp
        initPS <- initializeVerification' jsc ms bs cl
        liftIO $ printOutLn opts Debug $ "Overriding: " ++ show (map specName ovds)
        mapM_ (overrideFromSpec jsc (specPos ms)) ovds
        liftIO $ printOutLn opts Debug $ "Running method: " ++ specName ms
        -- Execute code.
        run
        liftIO $ printOutLn opts Debug $ "Checking final state"
        pvc <- checkFinalState jsc ms bs cl initPS
        let pvcs = [pvc] -- Only one for now, but that might change
        liftIO $ printOutLn opts ExtraDebug "Verifying the following:"
        liftIO $ mapM_ (printOutLn opts ExtraDebug . show . ppPathVC) pvcs
        let validator script = runValidation (prover script) vp jsc pvcs
        case jsTactic setupRes of
          Skip -> liftIO $ printOutLn opts Warn $
                    "WARNING: skipping verification of " ++ specName ms
          RunVerify script ->
            liftIO $ fmap fst $ runTopLevel (validator script) ro rw
    endTime <- io $ getCurrentTime
    printOutLnTop Info $ "Successfully verified " ++ specName ms ++ overrideText ++
                    " (" ++ showDuration (diffUTCTime endTime startTime) ++ ")"
  unless (jsSimulate setupRes) $ printOutLnTop Warn $
    "WARNING: skipping simulation of " ++ specName ms
  return ms

doExtraChecks :: Options -> SharedContext -> Term -> IO ()
doExtraChecks opts bsc t = do
  when (extraChecks opts) $ do
    printOutLn opts Debug "Type checking goal..."
    tcr <- scTypeCheck bsc Nothing t
    case tcr of
      Left e -> printOutLn opts Warn $ unlines $
                "Ill-typed goal constructed." : prettyTCError e
      Right _ -> printOutLn opts Debug "Done."
  printOutLn opts ExtraDebug $ "Trying to prove: " ++ show t

showCexResults :: Options
               -> SharedContext
               -> SS.PPOpts
               -> JavaMethodSpecIR
               -> VerifyState
               -> [ExtCns Term]
               -> [(String, FirstOrderValue)]
               -> IO ()
showCexResults vpopts sc opts ms vs exts vals = do
  printOutLn vpopts Info $ "When verifying " ++ specName ms ++ ":"
  printOutLn vpopts Info $ "Proof of " ++ vsVCName vs ++ " failed."
  printOutLn vpopts Info $ "Counterexample:"
  let showVal v = show <$> (Cryptol.runEval SS.quietEvalOpts
                    (Cryptol.ppValue Cryptol.Concrete (cryptolPPOpts opts) (exportFirstOrderValue v)))
  mapM_ (\(n, v) -> do vdoc <- showVal v
                       printOutLn vpopts Info ("  " ++ n ++ ": " ++ vdoc)) vals
  if (length exts == length vals)
    then do let cexEval = cexEvalFn sc (zip exts (map snd vals))
            doc <- vsCounterexampleFn vs cexEval
            printOutLn vpopts Info (renderDoc doc)
    else do printOutLn vpopts Info $ "ERROR: Can't show result, wrong number of values"
            printOutLn vpopts Info $ "Constants: " ++ show (map ecName exts)
            printOutLn vpopts Info $ "Value names: " ++ show (map fst vals)
  fail "Proof failed."

mkMixedExpr :: Term -> JavaSetup MixedExpr
mkMixedExpr (asJavaExpr -> Just s) =
  (JE . fst) <$> getJavaExpr "mkMixedExpr" s
mkMixedExpr t = do
  sc <- lift getSharedContext
  let exts = getAllExts t
      extNames = map ecName exts
  jes <- mapM (getJavaExpr "mkMixedExpr") extNames
  fn <- liftIO $ scAbstractExts sc exts t
  return $ LE $ LogicExpr fn (map fst jes)

exportJSSType :: JavaType -> JavaSetup Type
exportJSSType jty =
  case jty of
    JavaBoolean     -> return BooleanType
    JavaByte        -> return ByteType
    JavaChar        -> return CharType
    JavaShort       -> return ShortType
    JavaInt         -> return IntType
    JavaLong        -> return LongType
    JavaFloat       -> return FloatType
    JavaDouble      -> return DoubleType
    JavaArray _ ety -> ArrayType <$> exportJSSType ety
    JavaClass name  -> return $ ClassType (mkClassName (dotsToSlashes name))

exportJavaType :: Codebase -> JavaType -> JavaSetup JavaActualType
exportJavaType cb jty =
  case jty of
    JavaBoolean     -> return $ PrimitiveType BooleanType
    JavaByte        -> return $ PrimitiveType ByteType
    JavaChar        -> return $ PrimitiveType CharType
    JavaShort       -> return $ PrimitiveType ShortType
    JavaInt         -> return $ PrimitiveType IntType
    JavaLong        -> return $ PrimitiveType LongType
    JavaFloat       -> return $ PrimitiveType FloatType
    JavaDouble      -> return $ PrimitiveType DoubleType
    JavaArray n t   -> ArrayInstance (fromIntegral n) <$> exportJSSType t
    JavaClass name  ->
      do cls <- liftIO $ lookupClass cb fixPos (mkClassName (dotsToSlashes name))
         return (ClassInstance cls)

checkCompatibleType
  :: SharedContext
  -> String
  -> JavaActualType
  -> Cryptol.Schema
  -> JavaSetup ()
checkCompatibleType _sc msg aty schema =
  case cryptolTypeOfActual aty of
    Nothing ->
      throwJava $ "Type is not translatable: " ++ show aty ++ " (" ++ msg ++ ")"
    Just lt -> do
      unless (Cryptol.Forall [] [] lt == schemaNoUser schema) $ throwJava $
        unlines [ "Incompatible type:"
                , "  Expected: " ++ Cryptol.pretty lt
                , "  Got: " ++ Cryptol.pretty schema
                , "  In context: " ++ msg
                ]

parseJavaExpr' :: (MonadIO m) =>
                  JSS.Codebase -> JSS.Class -> JSS.Method -> String
               -> m JavaExpr
parseJavaExpr' cb cls meth name =
  liftIO (runExceptT (parseJavaExpr cb cls meth name) >>= either fail return)

getJavaExpr :: String -> String -> JavaSetup (JavaExpr, JavaActualType)
getJavaExpr ctx name = do
  ms <- gets jsSpec
  let cb = specCodebase ms
      cls = specThisClass ms
      meth = specMethod ms
  e <- parseJavaExpr' cb cls meth name
  case Map.lookup e (bsActualTypeMap (specBehaviors ms)) of
    Just ty -> return (e, ty)
    Nothing -> throwJava $ renderDoc $
      hsep [ "Unknown expression", ftext name, "in",  ftext ctx ] <> "."
      <$$>
      ftext "Maybe you're missing a `java_var` or `java_class_var`?"

typeJavaExpr :: BuiltinContext -> String -> JavaType
             -> JavaSetup (JavaExpr, JavaActualType)
typeJavaExpr bic name ty = do
  ms <- gets jsSpec
  let cb = biJavaCodebase bic
  expr <- parseJavaExpr' cb (specThisClass ms) (specMethod ms) name
  jty' <- exportJSSType ty
  checkEqualTypes (exprType expr) jty' name
  aty <- exportJavaType cb ty
  return (expr, aty)

checkEqualTypes :: Type -> Type -> String -> JavaSetup ()
checkEqualTypes declared actual name =
  when (declared /= actual) $ throwJava $ show $
    hsep [ text "WARNING: Declared type"
         , text (show (ppType declared)) -- TODO: change pretty-printer
         , text "doesn't match actual type"
         , text (show (ppType actual)) -- TODO: change pretty-printer
         , text "for variable"
         , text name
         ]

modifySpec :: (JavaMethodSpecIR -> JavaMethodSpecIR) -> JavaSetup ()
modifySpec f = modify $ \st -> st { jsSpec = f (jsSpec st) }

javaPure :: JavaSetup ()
javaPure = return ()

javaNoSimulate :: JavaSetup ()
javaNoSimulate = modify (\s -> s { jsSimulate = False })

javaSatBranches :: Bool -> JavaSetup ()
javaSatBranches doSat = modify (\s -> s { jsSatBranches = doSat })

javaRequiresClass :: String -> JavaSetup ()
javaRequiresClass cls = modifySpec $ \ms ->
  let clss' = mkClassName (dotsToSlashes cls) : specInitializedClasses ms in
  ms { specInitializedClasses = clss' }

javaClassVar :: BuiltinContext -> Options -> String -> JavaType
             -> JavaSetup ()
javaClassVar bic _ name t = do
  (expr, aty) <- typeJavaExpr bic name t
  case aty of
    ClassInstance _ -> return ()
    _ -> throwJava "Can't use `java_class_var` with variable of non-class type."
  modifySpec (specAddVarDecl expr aty)

javaVar :: BuiltinContext -> Options -> String -> JavaType
        -> JavaSetup TypedTerm
javaVar bic _ name t = do
  (expr, aty) <- typeJavaExpr bic name t
  case aty of
    ClassInstance _ -> throwJava "Can't use `java_var` with variable of class type."
    _ -> return ()
  modifySpec (specAddVarDecl expr aty)
  let sc = biSharedContext bic
  case cryptolTypeOfActual aty of
    Nothing -> throwJava $ "Unsupported type for `java_var`: " ++ show aty
    Just cty ->
      liftIO $
      do lty <- importType sc emptyEnv cty
         v <- scJavaValue sc lty name
         return $ TypedTerm (Cryptol.tMono cty) v

javaMayAlias :: [String] -> JavaSetup ()
javaMayAlias exprs = do
  exprList <- mapM (getJavaExpr "java_may_alias") exprs
  forM_ exprList $ \(e, _) ->
    unless (isRefJavaExpr e) $ throwJava $
      "Can't use `java_may_alias` with non-reference variable: " ++
      ppJavaExpr e
  modifySpec (specAddAliasSet (map fst exprList))

javaAssert :: TypedTerm -> JavaSetup ()
javaAssert (TypedTerm schema v) = do
  unless (schemaNoUser schema == Cryptol.Forall [] [] Cryptol.tBit) $
    throwJava $ "java_assert passed expression of non-boolean type: " ++ show schema
  me <- mkMixedExpr v
  case me of
    LE le -> modifySpec (specAddAssumption le)
    JE je -> throwJava $ "Used java_assert with Java expression: " ++ show je

javaAssertEq :: BuiltinContext -> Options -> String -> TypedTerm -> JavaSetup ()
javaAssertEq bic _ name (TypedTerm schema t) = do
  (expr, aty) <- (getJavaExpr "java_assert_eq") name
  checkCompatibleType (biSharedContext bic) "java_assert_eq" aty schema
  me <- mkMixedExpr t
  modifySpec (specAddLogicAssignment fixPos expr me)

javaEnsureEq :: BuiltinContext -> Options -> String -> TypedTerm -> JavaSetup ()
javaEnsureEq bic _ name (TypedTerm schema t) = do
  ms <- gets jsSpec
  (expr, aty) <- (getJavaExpr "java_ensure_eq") name
  when (isArg (specMethod ms) expr && isScalarExpr expr) $ throwJava $
    "The `java_ensure_eq` function cannot be used " ++
    "to set the value of a scalar argument."
  checkCompatibleType (biSharedContext bic) "java_ensure_eq" aty schema
  me <- mkMixedExpr t
  cmd <- case (CC.unTerm expr, aty) of
    (_, ArrayInstance _ _) -> return (EnsureArray fixPos expr me)
    (InstanceField r f, _) -> return (EnsureInstanceField fixPos r f me)
    (StaticField f, _) -> return (EnsureStaticField fixPos f me)
    _ -> throwJava $ "invalid java_ensure target: " ++ name
  modifySpec (specAddBehaviorCommand cmd)

javaModify :: String -> JavaSetup ()
javaModify name = do
  ms <- gets jsSpec
  (expr, aty) <- (getJavaExpr "java_modify") name
  when (isArg (specMethod ms) expr && isScalarExpr expr) $ throwJava $
    "The `java_modify` function cannot be used " ++
    "to set the value of a scalar argument."
  cmd <- case (CC.unTerm expr, aty) of
    (_, ArrayInstance _ _) -> return (ModifyArray expr aty)
    (InstanceField r f, _) -> return (ModifyInstanceField r f)
    (StaticField f, _) -> return (ModifyStaticField f)
    _ -> throwJava $ "invalid java_modify target: " ++ name
  modifySpec (specAddBehaviorCommand cmd)

javaReturn :: TypedTerm -> JavaSetup ()
javaReturn (TypedTerm _ t) = do
  ms <- gets jsSpec
  let meth = specMethod ms
  case methodReturnType meth of
    Just _ty -> do
      -- TODO: check that types are compatible
      me <- mkMixedExpr t
      modifySpec (specAddBehaviorCommand (ReturnValue me))
    Nothing ->
      throwJava $ "can't use `java_return` on void method " ++ methodName meth

javaVerifyTactic :: ProofScript SatResult -> JavaSetup ()
javaVerifyTactic script =
  modify $ \st -> st { jsTactic = RunVerify script }

javaAllowAlloc :: JavaSetup ()
javaAllowAlloc = modifySpec specSetAllowAllocation
