{- |
Module      : SAWScript.JavaMethodSpec
Description : Interface to the Java symbolic simulator.
License     : BSD3
Maintainer  : atomb
Stability   : provisional
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DoAndIfThenElse #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}

module SAWScript.JavaMethodSpec
  ( JavaMethodSpecIR
  , specMethod
  , specName
  , specMethodClass
  , SymbolicRunHandler
  , initializeVerification'
  , runValidation
  , checkFinalState
  , overrideFromSpec
  , PathVC(..)
  , pvcgAssertEq
  , pvcgAssert
  , pvcgFail
  , ppPathVC
  , VerifyParams(..)
  , VerifyState(..)
  , EvalContext(..)
  ) where

-- Imports {{{1

#if !MIN_VERSION_base(4,8,0)
import Control.Applicative hiding (empty)
#endif
import Control.Lens
import Control.Monad
import Control.Monad.Cont
import Control.Monad.State
import Data.Function
import Data.List (intercalate, sortBy)
import qualified Data.Map.Strict as Map
import Data.Maybe
import qualified Data.Set as Set
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.HughesPJ as PP

import Language.JVM.Common (ppFldId)
import qualified SAWScript.CongruenceClosure as CC
import SAWScript.JavaExpr as TC
import SAWScript.Options hiding (Verbosity)
import qualified SAWScript.Options as Opts
import SAWScript.Utils
import SAWScript.JavaMethodSpecIR
import SAWScript.JavaMethodSpec.Evaluator
import SAWScript.JavaUtils
import SAWScript.PathVC
import SAWScript.Value (TopLevel, TopLevelRW(rwPPOpts), getTopLevelRW, io, printOutTop, printOutLnTop)
import SAWScript.VerificationCheck

import Data.JVM.Symbolic.AST (entryBlock)

import Verifier.Java.Simulator hiding (asBool, State, InvalidType)
import Verifier.Java.SAWBackend hiding (basic_ss)

import Verifier.SAW.Prelude
import Verifier.SAW.Recognizer
import Verifier.SAW.SharedTerm
import Verifier.SAW.TypedTerm

-- JSS Utilities {{{1

type Verbosity = Int

-- EvalContext {{{1

evalErrExpr :: ExprEvalError -> TC.JavaExpr
evalErrExpr (EvalExprUndefined e) = e
evalErrExpr (EvalExprUnknownArray e) = e
evalErrExpr (EvalExprUnknownLocal _ e) = e
evalErrExpr (EvalExprUnknownField _ e) = e
evalErrExpr (EvalExprBadJavaType _ e) = e
evalErrExpr (EvalExprBadLogicType _ _) =
  error "evalErrExpr: EvalExprBadLogicType"
evalErrExpr (EvalExprNoReturn e) = e

-- Method specification overrides {{{1
-- OverrideComputation definition {{{2

-- | State for running the behavior specifications in a method override.
data OCState = OCState {
         ocsLoc :: Breakpoint
       , ocsEvalContext :: !EvalContext
       , ocsResultState :: !SpecPathState
       , ocsErrors :: [OverrideError]
       }

data OverrideError
   = UndefinedExpr TC.JavaExpr
   | FalseAssertion Pos
   | AliasingInputs !TC.JavaExpr !TC.JavaExpr
   | JavaExceptionThrown Ref
   | SimException String
   | InvalidType String
   | Abort
   deriving (Show)

ppOverrideError :: OverrideError -> String
ppOverrideError (UndefinedExpr expr) =
  "Could not evaluate " ++ show (TC.ppJavaExpr expr) ++ "."
ppOverrideError (FalseAssertion p)   =
  "Assertion at " ++ show p ++ " is false."
ppOverrideError (AliasingInputs x y) =
 "The expressions " ++ show (TC.ppJavaExpr x) ++ " and " ++
 show (TC.ppJavaExpr y) ++
 " point to the same reference, but are not allowed to alias each other."
ppOverrideError (JavaExceptionThrown _) = "A Java exception was thrown."
ppOverrideError (SimException s)     = "Simulation exception: " ++ s ++ "."
ppOverrideError (InvalidType ty)     =
  "Invalid type in modify clause: " ++ show ty
ppOverrideError Abort                = "Path was aborted."

data OverrideResult
   = SuccessfulRun (Path SharedContext) (Maybe Breakpoint) (Maybe SpecJavaValue)
   | FailedRun (Path SharedContext) (Maybe Breakpoint) [OverrideError]

type RunResult = ( Path SharedContext
                 , Maybe Breakpoint
                 , Either [OverrideError] (Maybe SpecJavaValue)
                 )

orParseResults :: [OverrideResult] -> [RunResult]
orParseResults l =
  [ (ps, block, Left  e) | FailedRun     ps block e <- l ] ++
  [ (ps, block, Right v) | SuccessfulRun ps block v <- l ]

type OverrideComputation m =
  ContT OverrideResult (StateT OCState (SAWJavaSim m))

ocError :: OverrideError -> OverrideComputation m ()
ocError e = modify $ \ocs -> ocs { ocsErrors = e : ocsErrors ocs }

-- OverrideComputation utilities {{{2

-- | Runs an evaluate within an override computation.
ocEval :: (EvalContext -> ExprEvaluator b)
       -> (b -> OverrideComputation m ())
       -> OverrideComputation m ()
ocEval fn m = do
  ec <- gets ocsEvalContext
  res <- runEval (fn ec)
  case res of
    Left e  -> ocError $ UndefinedExpr (evalErrExpr e)
    Right v -> m v

ocDoesEval :: (EvalContext -> ExprEvaluator b)
           -> OverrideComputation m Bool
ocDoesEval fn = do
  ec <- gets ocsEvalContext
  res <- runEval (fn ec)
  return $ either (const False) (const True) res

-- Modify result state
ocModifyResultState :: (SpecPathState -> SpecPathState)
                    -> OverrideComputation m ()
ocModifyResultState fn = do
  bcs <- get
  put $! bcs { ocsResultState = fn (ocsResultState bcs) }

ocModifyResultStateIO :: (SpecPathState -> IO SpecPathState)
                      -> OverrideComputation m ()
ocModifyResultStateIO fn = do
  bcs <- get
  new <- liftIO $ fn $ ocsResultState bcs
  put $! bcs { ocsResultState = new }

ocSetReturnValue :: Maybe SpecJavaValue
                 -> OverrideComputation m ()
ocSetReturnValue mrv = do
  bcs <- get
  let ec = ocsEvalContext bcs
      ec' = ec { ecReturnValue = mrv }
  put $! bcs { ocsEvalContext = ec' }

ocSetJavaExpr :: JavaExpr -> SpecJavaValue
              -> OverrideComputation m ()
ocSetJavaExpr e v = do
  ocEval (setJavaExpr e v) $ \ec -> do
    modify $ \ocs -> ocs { ocsEvalContext = ec }
  -- Anything other than a local or the return value should be set in
  -- the result state, as well.
  case e of
    CC.Term (ReturnVal _ ) -> return ()
    CC.Term (Local _ _ _) -> ocError (UndefinedExpr e)
    CC.Term (InstanceField refExpr f) ->
      ocEval (evalJavaRefExpr refExpr) $ \lhsRef ->
      ocModifyResultState $ setInstanceFieldValuePS lhsRef f v
    CC.Term (StaticField f) ->
      ocModifyResultState $ setStaticFieldValuePS f v

-- | Add assumption for predicate.
ocAssert :: Pos -> String -> Term -> OverrideComputation m ()
ocAssert p _nm x = do
  sc <- (ecContext . ocsEvalContext) <$> get
  case asBool x of
    Just True -> return ()
    Just False -> ocError (FalseAssertion p)
    _ -> ocModifyResultStateIO (addAssertionPS sc x)

-- ocStep {{{2

ocStep :: BehaviorCommand -> OverrideComputation m ()
ocStep (EnsureInstanceField _pos refExpr f rhsExpr) =
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef ->
  ocEval (evalMixedExpr (fieldIdType f) rhsExpr) $ \value ->
  ocModifyResultState $ setInstanceFieldValuePS lhsRef f value
ocStep (EnsureStaticField _pos f rhsExpr) =
  ocEval (evalMixedExpr (fieldIdType f) rhsExpr) $ \value ->
  ocModifyResultState $ setStaticFieldValuePS f value
ocStep (EnsureArray _pos lhsExpr rhsExpr) =
  ocEval (evalJavaRefExpr lhsExpr) $ \lhsRef ->
  ocEval (evalMixedExprAsLogic (exprType lhsExpr) rhsExpr) $ \rhsVal -> do
    sc <- gets (ecContext . ocsEvalContext)
    ty <- liftIO $ scTypeOf sc rhsVal >>= scWhnf sc
    case ty of
      (isVecType (const (return ())) -> Just (n :*: _)) ->
        ocModifyResultState $ setArrayValuePS lhsRef (fromIntegral n) rhsVal
      _ -> ocError (InvalidType (show ty))
ocStep (ModifyInstanceField refExpr f) =
  ocEval (evalJavaRefExpr refExpr) $ \lhsRef -> do
    sc <- gets (ecContext . ocsEvalContext)
    let tp = fieldIdType f
        w = fromIntegral $ stackWidth tp
    logicType <- liftIO $ scBitvector sc (fromInteger w)
    n <- liftIO $ scFreshGlobal sc (TC.ppJavaExpr refExpr) logicType
    v <- liftIO $ mkJSSValue sc tp n
    ocModifyResultState $ setInstanceFieldValuePS lhsRef f v
ocStep (ModifyStaticField f) = do
  sc <- gets (ecContext . ocsEvalContext)
  let tp = fieldIdType f
      w = fromIntegral $ stackWidth tp
  logicType <- liftIO $ scBitvector sc (fromInteger w)
  n <- liftIO $ scFreshGlobal sc (ppFldId f) logicType
  v <- liftIO $ mkJSSValue sc tp n
  ocModifyResultState $ setStaticFieldValuePS f v
ocStep (ModifyArray refExpr ty) =
  ocEval (evalJavaRefExpr refExpr) $ \ref -> do
    sc <- gets (ecContext . ocsEvalContext)
    case ty of
      ArrayInstance n tp -> do
        rhsVal <- liftIO $ do
          elTy <- scBitvector sc (fromIntegral (stackWidth tp))
          lTm <- scNat sc (fromIntegral n)
          aty <- scVecType sc lTm elTy
          scFreshGlobal sc (TC.ppJavaExpr refExpr) aty
        ocModifyResultState $ setArrayValuePS ref (fromIntegral n) rhsVal
      _ -> ocError (InvalidType (show ty))
ocStep (ReturnValue expr) = do
  mrty <- gets (ecReturnType . ocsEvalContext)
  case mrty of
    Just rty ->
      ocEval (evalMixedExpr rty expr) $ \val ->
        ocSetReturnValue (Just val)
    Nothing -> fail "Return type specification given for method of type void."

-- Executing overrides {{{2

execBehavior :: Method
             -> BehaviorSpec
             -> SharedContext
             -> Maybe Ref
             -> [(LocalVariableIndex, SpecJavaValue)]
             -> SpecPathState
             -> SAWJavaSim m [RunResult]
execBehavior meth bsl sc mbThis argLocals ps = do

  -- Get state of current execution path in simulator.
  fmap orParseResults $ forM [bsl] $ \bs -> do
    let ec = EvalContext { ecContext = sc
                         , ecLocals =  Map.fromList $
                                       case mbThis of
                                       Just th -> (0, RValue th) : argLocals
                                       Nothing -> argLocals
                         , ecReturnType = methodReturnType meth
                         , ecReturnValue = Nothing
                         , ecPathState = ps
                         }
    let initOCS =
          OCState { ocsLoc = bsLoc bs
                  , ocsEvalContext = ec
                  , ocsResultState = ps
                  , ocsErrors = []
                  }
    let resCont () = do
          OCState { ocsLoc = loc
                  , ocsResultState = resPS
                  , ocsEvalContext = ecres
                  , ocsErrors = l } <- get
          return $
            if null l then
              SuccessfulRun resPS (Just loc) (ecReturnValue ecres)
            else
              FailedRun resPS (Just loc) l
    flip evalStateT initOCS $ flip runContT resCont $ do
       -- If any of the reference expressions mentioned in the spec
       -- doesn't already evaluate to a reference, we need to allocate
       -- it.
       forM_ (sortBy (compare `on` exprDepth) (bsRefExprs bsl)) $ \e -> do
         exists <- ocDoesEval (evalJavaExpr e)
         unless exists $ do
           r <- lift $ lift $ genRef (exprType e)
           ocSetJavaExpr e (RValue r)

       ec' <- gets ocsEvalContext
       -- Check that all expressions that reference each other may do so.
       do -- Build map from references to expressions that map to them.
          let exprs = bsRefExprs bs
          ocEval (\_ -> mapM (flip evalJavaRefExpr ec') exprs) $ \refs -> do
            let refExprMap =
                  Map.fromListWith (++) $ refs `zip` [[e] | e <- exprs]
            --- Get counterexamples.
            let mayAliasSet = bsMayAliasSet bs
            let badPairs = catMaybes
                         $ map (\cl -> CC.checkEquivalence cl mayAliasSet)
                         $ Map.elems refExprMap
            -- Throw error if counterexample is found.
            case badPairs of
              [] -> return ()
              (x,y):_ -> ocError (AliasingInputs x y)
       -- Verify the initial logic assignments
       forM_ (bsLogicAssignments bs) $ \(pos, lhs, rhs) -> do
         ocEval (evalJavaExprAsLogic lhs) $ \lhsVal ->
           ocEval (evalMixedExprAsLogic (exprType lhs) rhs) $ \rhsVal ->
             ocAssert pos "Override value assertion"
                =<< liftIO (scEq sc lhsVal rhsVal)
       -- Verify assumptions
       forM_ (bsAssumptions bs) $ \le -> do
         ocEval (evalLogicExpr le) $ \assumptions ->
           ocAssert (PosInternal "assumption") "Override assumption check" assumptions
       -- Execute statements.
       mapM_ ocStep (bsCommands bs)

checkClassesInitialized :: MonadSim SharedContext m =>
                           Pos -> String -> [ClassName]
                        -> SAWJavaSim m ()
checkClassesInitialized pos nm requiredClasses = do
  forM_ requiredClasses $ \c -> do
    mem <- getMem (PP.text "checkClassesInitialized")
    let status = Map.lookup c (mem ^. memInitialization)
    when (status /= Just Initialized) $
      let msg = "The method spec \'" ++ nm ++
                "\' requires that the class " ++ slashesToDots (unClassName c) ++
                " is initialized.  SAWScript does not " ++
                "currently support methods that initialize new classes."
       in throwIOExecException pos (ftext msg) ""

execOverride :: MonadSim SharedContext m
             => SharedContext
             -> Pos
             -> JavaMethodSpecIR
             -> Maybe Ref
             -> [Value Term]
             -> SAWJavaSim m ()
execOverride sc pos ir mbThis args = do
  -- Execute behaviors.
  let bsl = specBehaviors ir -- Map.lookup (BreakPC 0) (specBehaviors ir) -- TODO
  let method = specMethod ir
      argLocals = map (localIndexOfParameter method) [0..] `zip` args
  -- Check class initialization.
  checkClassesInitialized pos (specName ir) (specInitializedClasses ir)
  initPS <- getPath "execOverride"
  res <- execBehavior method bsl sc mbThis argLocals initPS
  -- Create function for generation resume actions.
  case res of
    [(_, _, Left el)] -> do
      let msg = "Unsatisified assertions in " ++ specName ir ++ ":\n"
                ++ intercalate "\n" (map ppOverrideError el)
      fail msg
    [(ps, _, Right mval)] ->
      modifyPathM_ (PP.text "path result") $ \_ ->
        return $
        case (mval, ps ^. pathStack) of
          -- If the current path stack is empty, the result of the
          -- override is the return value of the current method.
          (_, [])     -> ps & set pathRetVal mval
          -- If the current path stack is non-empty and the override
          -- returned a value, put it on the operand stack of the
          -- current call frame.
          (Just val, (f:fr)) -> ps & set pathStack  (f' : fr)
            where f' = f & cfOpds %~ (val :)
          -- If the current path stack is non-empty and the override
          -- returned no value, leave the state alone.
          (Nothing,  _:_)    -> ps
    [] -> fail "Zero paths returned from override execution."
    _  -> fail "More than one path returned from override execution."

-- | Add a method override for the given method to the simulator.
overrideFromSpec :: MonadSim SharedContext m =>
                    SharedContext
                 -> Pos
                 -> JavaMethodSpecIR
                 -> SAWJavaSim m ()
overrideFromSpec de pos ir
  | methodIsStatic method =
      overrideStaticMethod cName key $ \args ->
        execOverride de pos ir Nothing args
  | otherwise =
      overrideInstanceMethod cName key $ \thisVal args ->
        execOverride de pos ir (Just thisVal) args
 where cName = className (specMethodClass ir)
       method = specMethod ir
       key = methodKey method

data VerifyParams = VerifyParams
  { vpCode    :: Codebase
  , vpContext :: SharedContext
  , vpOpts    :: Options
  , vpSpec    :: JavaMethodSpecIR
  , vpOver    :: [JavaMethodSpecIR]
  }

type SymbolicRunHandler =
  SharedContext -> [PathVC Breakpoint] -> TopLevel ()
type Prover =
  VerifyState -> Int -> Term -> TopLevel ()

runValidation :: Prover -> VerifyParams -> SymbolicRunHandler
runValidation prover params sc results = do
  let ir = vpSpec params
      printLn      = printOutLnTop
  opts <- fmap rwPPOpts getTopLevelRW
  forM_ results $ \pvc -> do
    let mkVState nm cfn =
          VState { vsVCName = nm
                 , vsMethodSpec = ir
                 , vsVerbosity = case Opts.verbLevel (vpOpts params) of
                                    Opts.Silent              -> 0
                                    Opts.OnlyCounterExamples -> 0
                                    Opts.Error               -> 1
                                    Opts.Warn                -> 2
                                    Opts.Info                -> 3
                                    _                        -> 4
                 , vsCounterexampleFn = cfn
                 , vsStaticErrors = pvcStaticErrors pvc
                 }
    if null (pvcStaticErrors pvc) then
     forM_ (zip [0..] (pvcChecks pvc)) $ \(n, vc) -> do
       let vs = mkVState (vcName vc) (vcCounterexample sc opts vc)
       g <- io $ scImplies sc (pvcAssumptions pvc) =<< vcGoal sc vc
       printOutTop Debug $ "Checking " ++ vcName vc
       printOutTop ExtraDebug $ " (" ++ scPrettyTerm defaultPPOpts g ++ ")"
       printOutTop Debug ""
       prover vs n g
    else do
      let vsName = "an invalid path"
      let vs = mkVState vsName (\_ -> return $ vcat (pvcStaticErrors pvc))
      false <- io $ scBool sc False
      g <- io $ scImplies sc (pvcAssumptions pvc) false
      printLn Info $ "Checking " ++ vsName
      printLn Info $ show $ pvcStaticErrors pvc
      printLn Debug $ "Calling prover to disprove " ++
                 scPrettyTerm defaultPPOpts (pvcAssumptions pvc)
      prover vs 0 g

data VerifyState = VState {
         vsVCName :: String
       , vsMethodSpec :: JavaMethodSpecIR
       , vsVerbosity :: Verbosity
         -- | Starting Block is used for checking VerifyAt commands.
       -- , vsFromBlock :: BlockId
         -- | Evaluation context used for parsing expressions during
         -- verification.
       -- , vsEvalContext :: EvalContext
       , vsCounterexampleFn :: CounterexampleFn
       , vsStaticErrors :: [Doc]
       }

{- Alternative implementation of JavaMethodSpec -}

initializeVerification' :: MonadSim SharedContext m
                        => SharedContext
                           -- ^ The SharedContext for creating new symbolic
                           -- expressions.
                        -> JavaMethodSpecIR
                           -- ^ The specification of the overall method.
                        -> BehaviorSpec
                           -- ^ The particular behavioral specification that
                           -- we are checking.
                        -> RefEquivConfiguration
                           -- ^ The particular relationship between which references
                           -- alias each other for verification purposes.
                        -> SAWJavaSim m SpecPathState
initializeVerification' sc ir bs refConfig = do
  -- Generate a reference for each reference equivalence class that
  -- isn't entirely involved in a return expression. Sort by depth so
  -- that we create enclosing objects before enclosed objects.
  let refConfig' = sortBy (compare `on` (maximum . map exprDepth . fst)) $
                   filter (not . all containsReturn . fst) refConfig
  exprRefs <- mapM (genRef . jssTypeOfActual . snd) refConfig'
  let refAssignments = (exprRefs `zip` map fst refConfig')
      pushFrame cs = case mcs' of
                       Nothing -> fail "internal: failed to push call frame"
                       Just cs' -> return cs'
        where
          mcs' = pushCallFrame
                 (className (specMethodClass ir))
                 (specMethod ir)
                 entryBlock -- FIXME: not the right block
                 Map.empty
                 cs
  forM_ (specInitializedClasses ir) initializeClass
  modifyCSM_ pushFrame
  forM_ refAssignments $ \(r, cl) ->
    forM_ cl $ \e -> writeJavaValue e (RValue r)
  lcs <- liftIO $ bsLogicClasses bs refConfig'
  case lcs of
    Nothing ->
      let msg = "Unresolvable cyclic dependencies between assumptions."
      in throwIOExecException (specPos ir) (ftext msg) ""
    Just assignments -> mapM_ (\(l, t, r) -> setClassValues sc l t r) assignments
  getPath (PP.text "initializeVerification")

evalLogicExpr' :: MonadSim SharedContext m =>
                  SharedContext -> LogicExpr
               -> SAWJavaSim m Term
evalLogicExpr' sc initExpr = do
  let exprs = logicExprJavaExprs initExpr
  args <- forM exprs $ \expr -> do
    t <- readJavaTermSim sc expr
    return (expr, t)
  let argMap = Map.fromList args
      argTerms = mapMaybe (\k -> Map.lookup k argMap) $
                 logicExprJavaExprs initExpr
  liftIO $ useLogicExpr sc initExpr argTerms

resolveClassRHS :: MonadSim SharedContext m =>
                   SharedContext
                -> JavaExpr
                -> JavaActualType
                -> [LogicExpr]
                -> SAWJavaSim m TypedTerm
resolveClassRHS sc e tp [] = do
  mlty <- liftIO $ TC.narrowTypeOfActual sc tp
  case (mlty, tp) of
    (Just lty, PrimitiveType pt) | pt /= LongType -> do
      liftIO $ (scFreshGlobal sc (jeVarName e) lty >>=
                mkTypedTerm sc)
    (Just lty, _) -> do
       liftIO $ (scFreshGlobal sc (jeVarName e) lty >>= mkTypedTerm sc)
    (Nothing, _) ->
      fail $ "Can't convert Java type to logic type: " ++
             show (TC.ppActualType tp)
resolveClassRHS sc _ _ [r] = do
  t <- evalLogicExpr' sc r
  liftIO $ mkTypedTerm sc t
resolveClassRHS _ _ _ _ =
  fail "Not yet implemented."

setClassValues :: (MonadSim SharedContext m) =>
                  SharedContext
               -> [JavaExpr]
               -> JavaActualType
               -> [LogicExpr]
               -> SAWJavaSim m ()
setClassValues sc l tp rs =
  forM_ l $ \e ->
    unless (containsReturn e) $ do
      t <- resolveClassRHS sc e tp rs
      writeJavaTerm sc e t

valueEqTerm :: (Functor m, Monad m, MonadIO m) =>
               SharedContext
            -> String
            -> SpecPathState
            -> Type
            -> SpecJavaValue
            -> Term
            -> StateT (PathVC Breakpoint) m ()
valueEqTerm sc name ps ty v t = do
  t' <- termOfValue sc ps ty v
  pvcgAssertEq name t' t

valueEqValue :: (Functor m, Monad m, MonadIO m) =>
               SharedContext
            -> String
            -> SpecPathState
            -> SpecJavaValue
            -> SpecPathState
            -> SpecJavaValue
            -> StateT (PathVC Breakpoint) m ()
valueEqValue _ _ _ (IValue i) _ (IValue i') | i == i' = return ()
valueEqValue _ _ _ (LValue l) _ (LValue l') | l == l' = return ()
valueEqValue _ _ _ (DValue d) _ (DValue d') | isNaN d && isNaN d' = return ()
valueEqValue _ _ _ (DValue d) _ (DValue d') | d == d' = return ()
valueEqValue _ _ _ (FValue f) _ (FValue f') | isNaN f && isNaN f' = return ()
valueEqValue _ _ _ (FValue f) _ (FValue f') | f == f' = return ()
valueEqValue _ _ _ (RValue r) _ (RValue r') | r == r' = return ()
valueEqValue _sc name _ (IValue t) _ (IValue t') = do
  pvcgAssertEq name t t'
valueEqValue _ name _ (LValue t) _ (LValue t') =
  pvcgAssertEq name t t'
valueEqValue _ name ps (RValue r) ps' (RValue r') = do
  let ma = Map.lookup r (ps ^. pathMemory . memScalarArrays)
      ma' = Map.lookup r' (ps' ^. pathMemory . memScalarArrays)
  case (ma, ma') of
    (Just (len, t), Just (len', t'))
      | len == len' -> pvcgAssertEq name t t'
      | otherwise -> fail $ "valueEqValue: array sizes don't match: " ++ show (len, len')
    _ -> fail $ "valueEqValue: " ++ name ++ ": ref does not point to array"
valueEqValue _ name _ v _ v' = fail $ "valueEqValue: " ++ name ++ ": unspported value type: " ++ show v ++ ", " ++ show v'

readJavaValueVerif :: (Functor m, Monad m) =>
                      VerificationState
                   -> Path' Term
                   -> JavaExpr
                   -> m SpecJavaValue
readJavaValueVerif vs ps refExpr = do
  let initPS = vsInitialState vs
  readJavaValue ((^. cfLocals) <$> currentCallFrame initPS) ps refExpr

checkStep :: (Functor m, Monad m, MonadIO m) =>
             VerificationState
          -> SpecPathState
          -> BehaviorCommand
          -> StateT (PathVC Breakpoint) m ()
checkStep vs ps (ReturnValue expr) = do
  let mrty = methodReturnType (specMethod (vsSpec vs))
  t <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) expr
  case (ps ^. pathRetVal, mrty) of
    (Just rv, Just rty) -> valueEqTerm (vsContext vs) "return" ps rty rv t
    (Nothing, _) -> fail "Return specification provided, but method did not return a value."
    (_, Nothing) -> fail "Return specification provided, but method has void type."
checkStep vs ps (EnsureInstanceField _pos refExpr f rhsExpr) = do
  rv <- readJavaValueVerif vs ps refExpr
  case rv of
    RValue ref -> do
      let mfv = getInstanceFieldValuePS ps ref f
      case mfv of
        Just fv -> do
          ft <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
          valueEqTerm (vsContext vs) (ppJavaExpr refExpr ++ "." ++ fieldIdName f) ps (fieldIdType f) fv ft
        Nothing  -> fail "Invalid instance field in java_ensure_eq."
    _ -> fail "Left-hand side of . did not evaluate to a reference."
checkStep vs ps (EnsureStaticField _pos f rhsExpr) = do
  let mfv = getStaticFieldValuePS ps f
  ft <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
  case mfv of
    Just fv -> valueEqTerm (vsContext vs) (ppFldId f) ps (fieldIdType f) fv ft
    Nothing -> fail "Invalid static field in java_ensure_eq."
checkStep _vs _ps (ModifyInstanceField _refExpr _f) = return ()
checkStep _vs _ps (ModifyStaticField _f) = return ()
checkStep vs ps (EnsureArray _pos refExpr rhsExpr) = do
  rv <- readJavaValueVerif vs ps refExpr
  t <- liftIO $ mixedExprToTerm (vsContext vs) (vsInitialState vs) rhsExpr
  case rv of
    RValue (Ref _ ty) ->
      valueEqTerm (vsContext vs) (ppJavaExpr refExpr) ps ty rv t
    _ -> fail "Non-reference value in EnsureArray"
checkStep _vs _ps (ModifyArray _refExpr _aty) = return ()

data VerificationState = VerificationState
                         { vsContext :: SharedContext
                         , vsSpec :: JavaMethodSpecIR
                         , vsInitialState :: SpecPathState
                         }

checkFinalState :: MonadSim SharedContext m =>
                   SharedContext
                -> JavaMethodSpecIR
                -> BehaviorSpec
                -> RefEquivConfiguration
                -> SpecPathState
                -> SAWJavaSim m (PathVC Breakpoint)
checkFinalState sc ms bs cl initPS = do
  let st = VerificationState { vsContext = sc
                             , vsSpec = ms
                             , vsInitialState = initPS
                             }
      cmds = bsCommands bs
  finalPS <- getPath "checkFinalState"
  let maybeRetVal = finalPS ^. pathRetVal
      initLocals = (^. cfLocals) <$> currentCallFrame initPS
  refList <- forM (concatMap fst cl) $ \e -> do
      rv <- readJavaValue initLocals finalPS e
      case rv of
        RValue r -> return (r, e)
        _ -> fail "internal: refMap"
  let refMap = Map.fromList refList
  assumptions <- liftIO $ evalAssumptions sc initPS (specAssumptions ms)
  let initState  =
        PathVC { pvcStartLoc = bsLoc bs
               , pvcEndLoc = Nothing
               , pvcAssumptions = assumptions
               , pvcStaticErrors = []
               , pvcChecks = []
               }
  let mentionedSFields =
        Set.fromList $
        [ fid | EnsureStaticField _ fid _ <- cmds] ++
        [ fid | ModifyStaticField fid <- cmds ]
      mentionedIFieldExprs =
        [ (e, fid) | EnsureInstanceField _ e fid _ <- cmds] ++
        [ (e, fid) | ModifyInstanceField e fid <- cmds ]
      mentionedArrayExprs =
        [ e | EnsureArray _ e _ <- cmds] ++
        [ e | ModifyArray e _ <- cmds ]
  mentionedIFields <- forM mentionedIFieldExprs $ \(e, fid) -> do
      -- TODO: best combination of initLocals and finalPS unclear here.
      rv <- readJavaValue initLocals finalPS e
      case rv of
        RValue r -> return (r, fid)
        _ -> fail "internal: mentionedIFields"
  mentionedArrays <- forM mentionedArrayExprs $ \e -> do
      -- TODO: best combination of initLocals and finalPS unclear here.
      rv <- readJavaValue initLocals finalPS e
      case rv of
        RValue r -> return r
        _ -> fail "internal: mentionedArrays"
  let mentionedIFieldSet = Set.fromList mentionedIFields
  let mentionedArraySet = Set.fromList mentionedArrays
  let mcf = currentCallFrame initPS
  args <- case mcf of
            Just cf -> return (Map.elems (cf ^. cfLocals))
            Nothing -> fail "internal: no call frame in initial path state"
  let reachable = reachableRefs finalPS (maybeToList maybeRetVal ++ args)
  flip execStateT initState $ do
    mapM_ (checkStep st finalPS) cmds
    let initMem = initPS ^. pathMemory
        finalMem = finalPS ^. pathMemory
        initRefArrays = initMem ^. memRefArrays
        finalRefArrays = finalMem ^. memRefArrays
    when (initMem ^. memInitialization /= finalMem ^. memInitialization) $
      let newClasses = Map.keys ((finalMem ^. memInitialization) `Map.difference`
                                 (initMem ^. memInitialization)) in
      unless (specAllowAlloc ms) $
        pvcgFail (text ("Initializes extra classes " ++ show newClasses))
    when (initMem ^. memClassObjects /= finalMem ^. memClassObjects) $
      pvcgFail "Allocates a class object."
    when (Map.keys initRefArrays /= Map.keys finalRefArrays) $
      unless (specAllowAlloc ms) $
        pvcgFail "Allocates a reference array"
    forM_ (Map.toList initRefArrays) $ \(r, a) ->
      case Map.lookup r finalRefArrays of
        Just a' -> when (a /= a') $ pvcgFail "Modifies a reference array."
        Nothing -> pvcgFail "Reference array disappeared?"
    forM_ (Map.toList (finalMem ^. memStaticFields)) $ \(f, fval) ->
      unless (Set.member f mentionedSFields) $
        unless(isArrayType (fieldIdType f)) $
          let fieldDesc = unClassName (fieldIdClass f) ++ "." ++ fieldIdName f in
          case Map.lookup f (initMem ^. memStaticFields) of
            Nothing -> pvcgFail $ hsep
              [ ftext "Modifies the unspecified static field"
              , ftext fieldDesc
              , "of type"
              , ftext (show (fieldIdType f))
              ]
            Just ival -> valueEqValue sc fieldDesc initPS ival finalPS fval
    forM_ (Map.toList (finalMem ^. memInstanceFields)) $ \((ref, f), fval) -> do
      unless (Set.member (ref, f) mentionedIFieldSet) $
        when (ref `Set.member` reachable && not (isArrayType (fieldIdType f))) $
        let fname =
              case Map.lookup ref refMap of
                Just e -> ppJavaExpr e ++ "." ++ fieldIdName f
                Nothing -> "field " ++ fieldIdName f ++  " of a new object"
        in
        case Map.lookup (ref, f) (initMem ^. memInstanceFields) of
          Nothing -> pvcgFail $ hsep
            [ ftext "Modifies the unspecified instance field"
            , ftext fname
            , "of type"
            , ftext (show (fieldIdType f))
            ]
          Just ival -> do
            valueEqValue sc fname initPS ival finalPS fval
    forM_ (Map.toList (finalMem ^. memScalarArrays)) $ \(ref, (flen, fval)) ->
      unless (Set.member ref mentionedArraySet) $
      when (ref `Set.member` reachable) $
      case Map.lookup ref (initMem ^. memScalarArrays) of
        Nothing -> unless (specAllowAlloc ms) $
                   pvcgFail "Allocates scalar array."
        Just (ilen, ival)
          | ilen == flen ->
              let aname =
                    case Map.lookup ref refMap of
                      Just e -> ppJavaExpr e
                      Nothing -> "a new array"
              in
              pvcgAssertEq aname ival fval -- TODO: name
          | otherwise -> pvcgFail $ hsep
            [ "Array changed size from"
            , int (fromIntegral ilen)
            , "to"
            , int (fromIntegral flen)
            ]
    -- TODO: check that return value has been specified if method returns a value
    pvcgAssert "final assertions" (finalPS ^. pathAssertions)
